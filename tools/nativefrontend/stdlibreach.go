package main

// stdlibreach.go — REACHABILITY-PRUNED emission of library units (stdlib
// source-through, slice 1; memo §2.1.1 "Emission is reachability-pruned
// from the program's roots", §6 mechanism 2).
//
// WHY PRUNE. A library package loaded whole would emit every declaration
// it contains — `unicode` alone is ~10k lines of RangeTable literals whose
// `$pkginit` would allocate thousands of tables for every program that
// imports `strings`. gc's own linker drops what is not referenced; the
// frontend does the equivalent at the SOURCE level, over go/types'
// resolved uses, so the wire carries exactly the library declarations the
// program can execute.
//
// THE WALK (a worklist to fixpoint over `types.Object`s):
//   roots — every declaration of every NON-library unit (they are emitted
//           whole, as before), plus, per library unit, its `init()`
//           functions (gc runs them whenever the package is linked in;
//           under the substitution table internal/bytealg has NONE —
//           index_generic.go declares no init(), so MaxLen stays at its
//           zero value, see stdlib-substitutions.tsv);
//   edges — for every identifier in a reached declaration, the object it
//           USES (info.Uses): a library FUNCTION marks its declaration; a
//           library METHOD marks its receiver TYPE; a package-level
//           library VARIABLE/CONSTANT marks its spec and its initializer
//           (all co-declared names); a library TYPE marks its spec AND
//           EVERY METHOD declared on it (the method-set completeness
//           invariant: a reached type carries its full method table with
//           BODIES, because a call dispatched through an interface names
//           no method identifier the walk could see — `err.Error()` on a
//           boxed `*strconv.NumError` must land on a bodied method, never
//           a stub); generic declarations are marked like any other (the
//           body is walked for its own edges; mono.go stencils them).
//   stops — the E5-T shadow-modeled types (importedmodel.go:
//           `strings.Builder`, `bytes.Buffer`) are NOT marked: the shadow
//           model stays the declaration of record until slice 2's
//           overlay retires it (their methods route to the harvested
//           model / its declaration-only stubs exactly as before).
//
// INITIALIZERS — the memo's rule ("package-level vars are lowered ONLY
// when reached", §2.1.1) and its soundness argument, stated once. An
// UNREACHED library variable's initializer is DROPPED, calls included
// (`errors.errorType = reflectlite.TypeOf(...)`, `strconv.ErrRange =
// errors.New(...)` when nothing reads them). Dropping it is unobservable
// iff the initializer has no effect beyond its own cell and cannot
// panic. Both hold for every package on the allowed list, and the
// argument is RECORDED per package in docs/stdlib-admission-register.md
// ("init-pure at the pin"): the purity census (memo §1.3, Appendix A)
// shows these packages reach no OS, no output and no runtime hook, and
// gc executes exactly these initializers at every `go run` of every
// program importing the package — a panicking one would have taken the
// oracle down on every row. A future allowed package with an init effect
// must argue its row there or be refused admission; the rule is NOT
// "unmodeled means effect-free" (the refuted H-11 reasoning, audit F1) —
// it is "the census says effect-free for THESE packages, and the
// differential exercises their init on every importing program".
//
// FAIL CLOSED: a package-scope library object with no declaration site in
// its unit (which cannot happen for a source-checked package) refuses the
// export rather than being silently left out of the wire.

import (
	"go/ast"
	"go/types"
)

// reachSet is a library unit's reached-declaration set. Every consumer
// in the emitter asks these maps; a nil *reachSet means "emit whole"
// (non-library units).
type reachSet struct {
	funcs  map[*ast.FuncDecl]bool
	types  map[*ast.TypeSpec]bool
	values map[*ast.ValueSpec]bool // package-level var and const specs
	// inits: the initializer RHS expressions of reached var specs — the
	// InitOrder entries $pkginit keeps (emit.go consults e.prunedInits
	// for the complement, populated in collectGlobals).
	inits map[ast.Expr]bool
}

func newReachSet() *reachSet {
	return &reachSet{
		funcs:  map[*ast.FuncDecl]bool{},
		types:  map[*ast.TypeSpec]bool{},
		values: map[*ast.ValueSpec]bool{},
		inits:  map[ast.Expr]bool{},
	}
}

// libIndex maps a library unit's objects to their declaration sites.
type libIndex struct {
	unit      *sourcePkg
	funcDecl  map[*types.Func]*ast.FuncDecl
	methodsOf map[*types.TypeName][]*ast.FuncDecl
	typeSpec  map[*types.TypeName]*ast.TypeSpec
	valueSpec map[types.Object]*ast.ValueSpec
}

func indexLibraryUnit(u *sourcePkg) (*libIndex, error) {
	idx := &libIndex{
		unit:      u,
		funcDecl:  map[*types.Func]*ast.FuncDecl{},
		methodsOf: map[*types.TypeName][]*ast.FuncDecl{},
		typeSpec:  map[*types.TypeName]*ast.TypeSpec{},
		valueSpec: map[types.Object]*ast.ValueSpec{},
	}
	for _, f := range u.files {
		for _, decl := range f.Decls {
			switch d := decl.(type) {
			case *ast.FuncDecl:
				fn, ok := u.info.Defs[d.Name].(*types.Func)
				if !ok || fn == nil {
					// `init` functions have no object in Defs' sense
					// (go/types records them as *types.Func too, but they
					// are never referenced); a nil here is an init or a
					// blank-named function — neither is reachable by use.
					continue
				}
				if d.Recv != nil {
					tn, ok := recvTypeName(fn)
					if !ok {
						return nil, unsup("stdlib source package %q: method %s has an unresolvable receiver type (fail closed)", u.path, d.Name.Name)
					}
					idx.methodsOf[tn] = append(idx.methodsOf[tn], d)
				}
				idx.funcDecl[fn] = d
			case *ast.GenDecl:
				for _, spec := range d.Specs {
					switch s := spec.(type) {
					case *ast.TypeSpec:
						tn, ok := u.info.Defs[s.Name].(*types.TypeName)
						if !ok || tn == nil {
							return nil, unsup("stdlib source package %q: type %s has no type object (fail closed)", u.path, s.Name.Name)
						}
						idx.typeSpec[tn] = s
					case *ast.ValueSpec:
						for _, n := range s.Names {
							if n.Name == "_" {
								continue
							}
							obj := u.info.Defs[n]
							if obj == nil {
								return nil, unsup("stdlib source package %q: %s has no object (fail closed)", u.path, n.Name)
							}
							idx.valueSpec[obj] = s
						}
					}
				}
			}
		}
	}
	return idx, nil
}

// recvTypeName resolves a method's receiver to its declared named type
// (pointer receivers dereferenced; generic receivers to the origin).
func recvTypeName(fn *types.Func) (*types.TypeName, bool) {
	sig, ok := fn.Type().(*types.Signature)
	if !ok || sig.Recv() == nil {
		return nil, false
	}
	t := sig.Recv().Type()
	if ptr, isPtr := t.(*types.Pointer); isPtr {
		t = ptr.Elem()
	}
	named, ok := types.Unalias(t).(*types.Named)
	if !ok {
		return nil, false
	}
	return named.Origin().Obj(), true
}

// computeLibraryReach runs the walk and stores each library unit's
// reachSet. Non-library units get none (emitted whole).
func computeLibraryReach(units []*sourcePkg) error {
	byPkg := map[*types.Package]*sourcePkg{}
	indexes := map[*sourcePkg]*libIndex{}
	anyLibrary := false
	for _, u := range units {
		byPkg[u.pkg] = u
		if u.library {
			anyLibrary = true
			idx, err := indexLibraryUnit(u)
			if err != nil {
				return err
			}
			indexes[u] = idx
			u.reached = newReachSet()
		}
	}
	if !anyLibrary {
		return nil
	}

	type item struct {
		unit *sourcePkg
		node ast.Node
	}
	var work []item
	push := func(u *sourcePkg, n ast.Node) { work = append(work, item{u, n}) }

	var markType func(lu *sourcePkg, tn *types.TypeName) error
	markFuncDecl := func(lu *sourcePkg, fd *ast.FuncDecl) {
		if !lu.reached.funcs[fd] {
			lu.reached.funcs[fd] = true
			push(lu, fd)
		}
	}
	markValue := func(lu *sourcePkg, obj types.Object) error {
		vs := indexes[lu].valueSpec[obj]
		if vs == nil {
			return unsup("stdlib source package %q: package-scope %s %s has no declaration site (fail closed)", lu.path, objKind(obj), obj.Name())
		}
		if lu.reached.values[vs] {
			return nil
		}
		lu.reached.values[vs] = true
		for _, v := range vs.Values {
			lu.reached.inits[v] = true
		}
		push(lu, vs)
		return nil
	}
	markType = func(lu *sourcePkg, tn *types.TypeName) error {
		if tn.Parent() != lu.pkg.Scope() {
			// A type declared inside a function body: its declaration is
			// part of the enclosing (reached) body — nothing to mark.
			return nil
		}
		if modeledImportedTypes[lu.path+"."+tn.Name()] != nil {
			return nil // E5-T shadow model is the declaration of record
		}
		ts := indexes[lu].typeSpec[tn]
		if ts == nil {
			return unsup("stdlib source package %q: package-scope type %s has no declaration site (fail closed)", lu.path, tn.Name())
		}
		if lu.reached.types[ts] {
			return nil
		}
		lu.reached.types[ts] = true
		push(lu, ts)
		for _, fd := range indexes[lu].methodsOf[tn] {
			markFuncDecl(lu, fd)
		}
		return nil
	}
	// markTypeOf marks every library NAMED type mentioned in a go/types
	// type — the types the AST does not spell: an iota const group's
	// implicitly repeated type (`ErrRange` in internal/strconv's `const (
	// ErrSyntax Error = iota + 1; ErrRange; …)` names `Error` only on
	// its first spec), an inferred `var x = f()`, a signature reached
	// through a method value. Belt to the identifier walk's braces.
	var markTypeOf func(t types.Type, depth int) error
	markTypeOf = func(t types.Type, depth int) error {
		if t == nil || depth > 24 {
			return nil
		}
		switch x := types.Unalias(t).(type) {
		case *types.Named:
			if lu := byPkg[x.Obj().Pkg()]; lu != nil && lu.library {
				if err := markType(lu, x.Origin().Obj()); err != nil {
					return err
				}
			}
			for i := 0; i < x.TypeArgs().Len(); i++ {
				if err := markTypeOf(x.TypeArgs().At(i), depth+1); err != nil {
					return err
				}
			}
		case *types.Pointer:
			return markTypeOf(x.Elem(), depth+1)
		case *types.Slice:
			return markTypeOf(x.Elem(), depth+1)
		case *types.Array:
			return markTypeOf(x.Elem(), depth+1)
		case *types.Chan:
			return markTypeOf(x.Elem(), depth+1)
		case *types.Map:
			if err := markTypeOf(x.Key(), depth+1); err != nil {
				return err
			}
			return markTypeOf(x.Elem(), depth+1)
		case *types.Struct:
			for i := 0; i < x.NumFields(); i++ {
				if err := markTypeOf(x.Field(i).Type(), depth+1); err != nil {
					return err
				}
			}
		case *types.Tuple:
			for i := 0; i < x.Len(); i++ {
				if err := markTypeOf(x.At(i).Type(), depth+1); err != nil {
					return err
				}
			}
		case *types.Signature:
			if err := markTypeOf(x.Params(), depth+1); err != nil {
				return err
			}
			return markTypeOf(x.Results(), depth+1)
		case *types.Interface:
			for i := 0; i < x.NumMethods(); i++ {
				if err := markTypeOf(x.Method(i).Type(), depth+1); err != nil {
					return err
				}
			}
		}
		return nil
	}
	markObject := func(obj types.Object) error {
		if obj == nil || obj.Pkg() == nil {
			return nil
		}
		lu := byPkg[obj.Pkg()]
		if lu == nil || !lu.library {
			return nil
		}
		switch o := obj.(type) {
		case *types.Func:
			o = o.Origin()
			if sig, isSig := o.Type().(*types.Signature); isSig && sig.Recv() != nil {
				if tn, named := recvTypeName(o); named {
					return markType(lu, tn)
				}
				// A method of an UNNAMED interface type (`err.(interface{
				// Unwrap() error })` in errors/wrap.go, `x.Is(target)`): it
				// has no declaration of its own — the dispatch lands on
				// whichever concrete method the value carries, which the
				// walk reaches through that type. Nothing to mark. (Audit
				// fix round B2: this used to fall through to the package-
				// level lookup and refuse the WHOLE export as "no
				// declaration site" — a regression vs main, where errors.Is
				// quarantined per declaration.)
				return nil
			}
			fd := indexes[lu].funcDecl[o]
			if fd == nil {
				return unsup("internal: stdlib source package %q: package-level function %s is not indexed to a declaration (a reachability-index invariant broke — fail closed)", lu.path, o.Name())
			}
			markFuncDecl(lu, fd)
			return markTypeOf(o.Type(), 0)
		case *types.Var:
			if o.IsField() || o.Parent() != lu.pkg.Scope() {
				return nil
			}
			if err := markValue(lu, o.Origin()); err != nil {
				return err
			}
			return markTypeOf(o.Type(), 0)
		case *types.Const:
			if o.Parent() != lu.pkg.Scope() {
				return nil
			}
			if err := markValue(lu, o); err != nil {
				return err
			}
			return markTypeOf(o.Type(), 0)
		case *types.TypeName:
			return markType(lu, o)
		}
		return nil
	}

	// Roots.
	for _, u := range units {
		for _, f := range u.files {
			for _, decl := range f.Decls {
				if !u.library {
					push(u, decl)
					continue
				}
				// A library unit's only roots are its init() functions:
				// package-variable initializers lower only when the
				// variable is reached (see the header's INITIALIZERS
				// paragraph for why dropping the rest is sound).
				if d, isFn := decl.(*ast.FuncDecl); isFn && d.Recv == nil && d.Name.Name == "init" {
					markFuncDecl(u, d)
				}
			}
		}
	}

	// Fixpoint.
	for len(work) > 0 {
		it := work[len(work)-1]
		work = work[:len(work)-1]
		var walkErr error
		ast.Inspect(it.node, func(n ast.Node) bool {
			if walkErr != nil {
				return false
			}
			// A direct CALL of a RETAINED shim member from a NON-library
			// unit (`strconv.ParseUint(s, 10, 64)`, `strings.Join(..)`)
			// lowers to the injected shim, not to the library function
			// (emitStdlibShimCall takes precedence): the callee is not
			// reached — only its arguments are walked. The VALUE shape
			// (`f := strings.Join`) and every library-internal call
			// reach the real declaration.
			if c, isCall := n.(*ast.CallExpr); isCall && !it.unit.library {
				if sel, isSel := c.Fun.(*ast.SelectorExpr); isSel {
					if x, isIdent := sel.X.(*ast.Ident); isIdent {
						if pn, isPkg := it.unit.info.Uses[x].(*types.PkgName); isPkg {
							if fns, shimmed := stdlibShimAllowlist[pn.Imported().Path()]; shimmed {
								if _, member := fns[sel.Sel.Name]; member {
									for _, a := range c.Args {
										ast.Inspect(a, func(m ast.Node) bool {
											if walkErr != nil {
												return false
											}
											if id, ok := m.(*ast.Ident); ok {
												if obj := it.unit.info.Uses[id]; obj != nil {
													walkErr = markObject(obj)
												}
											}
											return true
										})
									}
									return false
								}
							}
						}
					}
				}
			}
			id, ok := n.(*ast.Ident)
			if !ok {
				return true
			}
			if obj := it.unit.info.Uses[id]; obj != nil {
				walkErr = markObject(obj)
			}
			return true
		})
		if walkErr != nil {
			return walkErr
		}
	}
	return nil
}

func objKind(obj types.Object) string {
	switch obj.(type) {
	case *types.Var:
		return "variable"
	case *types.Const:
		return "constant"
	case *types.Func:
		return "function"
	case *types.TypeName:
		return "type"
	}
	return "object"
}

// checkUnsafeLayoutOpsLibrary is checkUnsafeLayoutOps (emit.go) for a
// LIBRARY unit: scanned over the REACHED declarations only. A layout
// operator inside a reached FUNCTION condemns that function to an H-3
// stub (e.forcedQuarantine, consumed by emitProgram's FuncDecl loop); one
// inside a reached var/const/type spec refuses the whole export (a folded
// layout constant launders into every use site — the same reasoning as
// the user-unit scan). Dot-imports of unsafe refuse outright, as there.
func (e *emitter) checkUnsafeLayoutOpsLibrary(u *sourcePkg) error {
	if u.reached == nil {
		return unsup("internal: library unit %q has no reachability set (fail closed)", u.path)
	}
	for _, f := range u.files {
		for _, imp := range f.Imports {
			if imp.Name != nil && imp.Name.Name == "." && imp.Path.Value == `"unsafe"` {
				return unsup("stdlib source package %q: import . \"unsafe\" at %s — a dot-import puts the layout operators outside the selector-based scan (fail closed)", u.path, e.fset.Position(imp.Pos()))
			}
		}
	}
	find := func(n ast.Node) (string, bool) {
		hit := ""
		ast.Inspect(n, func(x ast.Node) bool {
			if hit != "" {
				return false
			}
			sel, ok := x.(*ast.SelectorExpr)
			if !ok {
				return true
			}
			switch sel.Sel.Name {
			case "Sizeof", "Offsetof", "Alignof":
			default:
				return true
			}
			base, ok := ast.Unparen(sel.X).(*ast.Ident)
			if !ok {
				return true
			}
			if pn, ok := u.info.Uses[base].(*types.PkgName); ok && pn.Imported().Path() == "unsafe" {
				hit = "unsafe." + sel.Sel.Name + " at " + e.fset.Position(sel.Pos()).String()
				return false
			}
			return true
		})
		return hit, hit != ""
	}
	for fd := range u.reached.funcs {
		if site, hit := find(fd); hit {
			if e.forcedQuarantine == nil {
				e.forcedQuarantine = map[*ast.FuncDecl]string{}
			}
			e.forcedQuarantine[fd] = "stdlib source-through: " + u.path + "." + fd.Name.Name + " uses " + site +
				" — its folded value is gc's IMPLEMENTATION-SPECIFIC memory layout (spec#Size_and_alignment_guarantees forces only the fixed-width types); out of language, ledger row Package_unsafe (fail closed)"
		}
	}
	for ts := range u.reached.types {
		if site, hit := find(ts); hit {
			return unsup("stdlib source package %q: reached type %s mentions %s — a layout constant in a declaration would launder into every use (fail closed, whole export)", u.path, ts.Name.Name, site)
		}
	}
	for vs := range u.reached.values {
		if site, hit := find(vs); hit {
			return unsup("stdlib source package %q: reached var/const spec %s mentions %s — a folded layout constant would launder into every use (fail closed, whole export)", u.path, vs.Names[0].Name, site)
		}
	}
	return nil
}

// libraryDeclLabel is the `<path>.<Decl>` / `<path>.<Type>.<Method>`
// prefix of a library unit's quarantine reasons (audit fix round F5).
func (e *emitter) libraryDeclLabel(u *sourcePkg, d *ast.FuncDecl) string {
	if d.Recv != nil && len(d.Recv.List) > 0 {
		rt := d.Recv.List[0].Type
		if star, ok := rt.(*ast.StarExpr); ok {
			rt = star.X
		}
		if ix, ok := rt.(*ast.IndexExpr); ok {
			rt = ix.X
		}
		if il, ok := rt.(*ast.IndexListExpr); ok {
			rt = il.X
		}
		if id, ok := rt.(*ast.Ident); ok {
			return u.path + "." + id.Name + "." + d.Name.Name
		}
	}
	return u.path + "." + d.Name.Name
}

// isUnimplementedPanicBody reports whether a body is exactly
// `panic("unimplemented")` (audit fix round F7).
func isUnimplementedPanicBody(b *ast.BlockStmt) bool {
	if b == nil || len(b.List) != 1 {
		return false
	}
	es, ok := b.List[0].(*ast.ExprStmt)
	if !ok {
		return false
	}
	call, ok := es.X.(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return false
	}
	fn, ok := call.Fun.(*ast.Ident)
	if !ok || fn.Name != "panic" {
		return false
	}
	lit, ok := call.Args[0].(*ast.BasicLit)
	return ok && lit.Value == `"unimplemented"`
}
