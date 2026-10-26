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
//   stops — an E5-T shadow-modeled type (importedmodel.go) would not be
//           marked (the model would be the declaration of record); since
//           slice 2 retired the `strings.Builder`/`bytes.Buffer` models
//           only the sync/atomic wrappers remain, and `sync/atomic` is not
//           a library unit, so the stop is inert — kept as the invariant.
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
	"sort"
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
		// The CALLS in `defer`/`go` position of this body (the statement's
		// own `.Call`; ast.Inspect visits the statement before its call):
		// there the callee is a FUNCTION VALUE, and an intercepted member
		// is the real library member (its declaration reached, its
		// closure on the wire) — the emitter's DeferStmt/GoStmt arms
		// lower it through the ordinary value path (2026-10-25, backlog
		// row 50: the intercept applies in expression-statement position
		// only; the former by-name refusal of these shapes is retired).
		spawnCalls := map[*ast.CallExpr]bool{}
		ast.Inspect(it.node, func(n ast.Node) bool {
			if walkErr != nil {
				return false
			}
			switch st := n.(type) {
			case *ast.DeferStmt:
				spawnCalls[st.Call] = true
			case *ast.GoStmt:
				spawnCalls[st.Call] = true
			}
			// A direct CALL of a FRONTEND-INTERCEPTED library member from
			// a NON-library unit in EXPRESSION-STATEMENT position — a
			// retained direct-call shim (stdlibShimAllowlist; empty since
			// slice 2) or a machine-op member (frontendInterceptedLibraryMembers:
			// `slices.Sort` at an integer element kind, the `sortSlice`
			// op) — never lowers to the library function: the callee is
			// not reached, only its arguments are walked. The VALUE shape
			// (`f := slices.Sort[[]int]; f(s)` — a `func-value` of the
			// stencil, its closure on the wire), the `defer`/`go` shapes
			// (spawnCalls above), a call inside a USER GENERIC body (the
			// argument's type is the pre-stencil type parameter, never a
			// slice of an integer basic kind), a dot-imported `Sort(s)`
			// (a bare identifier, not a qualified selector) and every
			// library-internal call reach the real declaration and lower
			// as the real generic (review fix round F2/F3, 2026-10-25).
			if c, isCall := n.(*ast.CallExpr); isCall && !it.unit.library && !spawnCalls[c] {
				if sel, isSel := c.Fun.(*ast.SelectorExpr); isSel {
					if x, isIdent := sel.X.(*ast.Ident); isIdent {
						if pn, isPkg := it.unit.info.Uses[x].(*types.PkgName); isPkg {
							path := pn.Imported().Path()
							_, _, intercepted, ierr := interceptedLibraryCall(it.unit.info, c)
							if ierr != nil {
								walkErr = ierr
								return false
							}
							if fns, shimmed := stdlibShimAllowlist[path]; shimmed {
								_, intercepted2 := fns[sel.Sel.Name]
								intercepted = intercepted || intercepted2
							}
							if intercepted {
								{
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

// frontendInterceptedLibraryMembers: members of source-through library
// packages whose DIRECT CALL the emitter lowers to a machine op or a
// frontend desugar INSTEAD of the library body — so the reach walk must
// not mark the body reached (it would drag the real declaration and its
// closure onto the wire for nothing). Rendered in the admission register
// (class `intercept`), so widening this map fails scripts/check-stdlib-register.
// The reach walk and the emitter consult ONE predicate,
// interceptedLibraryCall (audit fix round F1 of 2026-09-04: the walk used
// to treat ANY direct `slices.Sort(s)` call as intercepted while the
// emitter intercepted only the ExprStmt shape — `defer slices.Sort(s)` /
// `go slices.Sort(s)` lowered the real generic with `math/bits.Len` pruned
// off the wire, a machine `stuck` where a refusal was owed). The predicate
// judges the CALL EXPRESSION; the POSITION rule is shared by construction:
// the walk excludes the `defer`/`go` statements' own calls (spawnCalls)
// and the emitter's DeferStmt/GoStmt arms never consult the predicate, so
// in spawn position the member is the real library function value with
// its closure on the wire (the former by-name refusal of those shapes,
// F1, is retired with the 2026-10-25 re-admission below).
//
// ONE entry since 2026-10-25 ([USER] ruling of 2026-10-25, backlog row 50
// option 1, relayed: a deliberate PARTIAL REVERSAL, for integer element
// kinds only, of memo §3 row M (lane fr4-rowm, 2026-09-04), which retired
// the same entry under the posture «gc's exact members source-through»;
// the sorted result of an integer slice is unique, so no observable
// result differs between the op and gc's pdqsort — only the step count,
// the trace and the detector's access events, which are not differential
// observations):
//   - `slices.Sort` → the `sortSlice` MACHINE OP (`Stmt.sortSlice`, the
//     `sort-slice` wire node; emit.go emitSortStmt) for a DIRECT call in
//     expression-statement position whose argument is a slice of an
//     INTEGER basic kind (`int`, `int8`…`int64`, `uint`, `uint8`…`uint64`,
//     `uintptr`, and every DEFINED type whose underlying is one — the
//     kinds `IntKind` has and `intElems`, the op's operand check,
//     admits). Everything else is the real generic through the
//     source-through unit, NOT a refusal: a string, float or other
//     non-integer element kind (rows slices/slices-sort-kinds/*,
//     slices/slices-sort-non-integer-refusal), `defer`/`go` of the
//     function value at any kind (rows stdlib-source/sort-op-shapes/*),
//     the VALUE shape (`f := slices.Sort[[]int]; f(s)` — a `func-value`
//     of the stencil with its pdqsort closure on the wire, runs
//     correctly), a call inside a USER GENERIC body
//     (`func sortAll[S ~[]E, E cmp.Ordered](s S) { slices.Sort(s) }`,
//     the `~int` / `interface{~[]int}` constraint forms — the predicate
//     judges the PRE-STENCIL type parameter, whose underlying is the
//     constraint interface, so the stencil lowers the generic), and a
//     dot-imported `Sort(s)` (a bare identifier is never a qualified
//     selector; the real function lowers). The raft-proofs customer's ask:
//     the raft-proofs repository's docs/2026-10-23_golean-ask-slices-sort.md
//     (a sibling checkout; no path into this tree).
//
// The former second entry, cmp.Compare's kind-dispatch desugar, stays
// RETIRED (2026-09-04, lane fr24, per the [USER] ruling of 2026-09-04,
// relayed, that with a plan in hand an honest red beats the desugar).
//
// A new entry is a register widening AND needs its arm in
// interceptedMemberArm's switch (the predicate fails closed on a listed
// member without an arm — see below).
var frontendInterceptedLibraryMembers = map[string]map[string]string{
	"slices": {"Sort": "the `sortSlice` MACHINE OP (Stmt.sortSlice, wire node `sort-slice`; emit.go emitSortStmt) for a DIRECT call in expression-statement position at an INTEGER element kind — int/int8..int64/uint/uint8..uint64/uintptr and defined types over them (the op's intElems operand check); every other shape is the real source-through generic, not a refusal: non-integer element kinds (rows slices/slices-sort-kinds/*), defer/go of the function value at any kind (rows stdlib-source/sort-op-shapes/*), the value shape `f := slices.Sort[[]int]; f(s)` (a func-value of the stencil, its closure on the wire), a call inside a user generic body (the pre-stencil type parameter is judged: the stencil lowers the generic) and a dot-imported `Sort(s)`; re-admitted 2026-10-25 ([USER] ruling, backlog row 50 option 1, relayed) as a deliberate partial reversal of memo §3 row M for integer kinds only — the sorted result is unique there, so no observable result differs; the op's specification is the kept equation family applyStmtOp_sortSlice*/retV_stmtOpK_sortSlice* (GoLean/GoCore/Equations.lean)"},
}

// interceptedLibraryCall reports whether a direct qualified CALL of a
// library member is one the FRONTEND intercepts (table above) — the one
// predicate both the reach walk (do not mark the callee) and the emitter
// (which lowering) consult, so they cannot disagree. The per-member
// conditions mirror the emitter's dispatch exactly:
//
//	slices.Sort  — intercepted iff the one argument is a slice whose
//	               element type's underlying is an integer basic kind
//	               (interceptSortSlice); the `sortSlice` op in ExprStmt
//	               position. Any other element kind: NOT intercepted, the
//	               real generic. Position (ExprStmt vs defer/go) is the
//	               callers' rule, shared by construction (see the table).
//
// A member listed in the table without an arm in interceptedMemberArm is
// a NAMED REFUSAL (fail closed), never "not intercepted".
func interceptedLibraryCall(info *types.Info, c *ast.CallExpr) (path, member string, intercepted bool, err error) {
	sel, isSel := c.Fun.(*ast.SelectorExpr)
	if !isSel {
		return "", "", false, nil
	}
	x, isIdent := sel.X.(*ast.Ident)
	if !isIdent {
		return "", "", false, nil
	}
	pn, isPkg := info.Uses[x].(*types.PkgName)
	if !isPkg {
		return "", "", false, nil
	}
	path, member = pn.Imported().Path(), sel.Sel.Name
	if _, listed := frontendInterceptedLibraryMembers[path][member]; !listed {
		return path, member, false, nil
	}
	return interceptedMemberArm(info, c, path, member)
}

// interceptedMemberArm is the per-member dispatch behind
// interceptedLibraryCall for a member the table LISTS. FAIL CLOSED (fr4-rowm
// audit fix round A6): a listed member with no arm here is a table/dispatch
// disagreement — the register counts it as intercepted while nothing
// intercepts it — so it is a NAMED REFUSAL, never "not intercepted" (which
// would silently lower the real body the register says is bypassed).
// Re-admitting a member adds its case here AND its table row.
func interceptedMemberArm(info *types.Info, c *ast.CallExpr, path, member string) (string, string, bool, error) {
	switch path + "." + member {
	case "slices.Sort":
		return path, member, interceptSortSlice(info, c), nil
	}
	return path, member, false, unsup("library member %s.%s is listed in frontendInterceptedLibraryMembers (register class `intercept`) but interceptedLibraryCall has no arm for it — table and dispatch disagree; refused rather than lowering the real body the register says is intercepted (fail closed)", path, member)
}

// interceptSortSlice: the `slices.Sort` arm's condition — ONE argument whose
// type's underlying is a slice of an INTEGER basic kind (go/types'
// IsInteger: int, int8…int64, uint, uint8…uint64, uintptr; a defined type
// over one qualifies through its underlying — `type sortIndex uint64`).
// These are exactly the kinds the machine op's operand check `intElems`
// admits (every one lowers to an `IntKind`; `emitType` refuses nothing
// here that the generic path would accept). A slice of anything else —
// strings, floats, complex, a struct, a pointer — is NOT intercepted and
// lowers through the real generic (`pdqsortOrdered` stenciled per element
// type), never a refusal. A non-slice argument or a wrong arity cannot
// type-check (`slices.Sort[S ~[]E, E cmp.Ordered]`), so go/types has
// refused the program before this runs; the emitter's guards keep the
// by-name refusal texts for a wire that somehow reaches them.
func interceptSortSlice(info *types.Info, c *ast.CallExpr) bool {
	if len(c.Args) != 1 {
		return false
	}
	tv, ok := info.Types[c.Args[0]]
	if !ok || tv.Type == nil {
		return false
	}
	sl, ok := tv.Type.Underlying().(*types.Slice)
	if !ok {
		return false
	}
	b, ok := sl.Elem().Underlying().(*types.Basic)
	return ok && b.Info()&types.IsInteger != 0
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
	// Visit the reached specs in SOURCE-POSITION order (BUG-091): these
	// loops return on the FIRST hit, so a map-order walk would make the
	// refusal text — and hence which declaration the export names —
	// vary between runs when two reached specs both mention a site.
	typeSpecs := make([]*ast.TypeSpec, 0, len(u.reached.types))
	for ts := range u.reached.types {
		typeSpecs = append(typeSpecs, ts)
	}
	sort.Slice(typeSpecs, func(i, j int) bool { return typeSpecs[i].Pos() < typeSpecs[j].Pos() })
	for _, ts := range typeSpecs {
		if site, hit := find(ts); hit {
			return unsup("stdlib source package %q: reached type %s mentions %s — a layout constant in a declaration would launder into every use (fail closed, whole export)", u.path, ts.Name.Name, site)
		}
	}
	valueSpecs := make([]*ast.ValueSpec, 0, len(u.reached.values))
	for vs := range u.reached.values {
		valueSpecs = append(valueSpecs, vs)
	}
	sort.Slice(valueSpecs, func(i, j int) bool { return valueSpecs[i].Pos() < valueSpecs[j].Pos() })
	for _, vs := range valueSpecs {
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
