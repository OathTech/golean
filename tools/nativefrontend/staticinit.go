package main

// staticinit.go — the BUG-061 guard: refuse, by name, the programs whose
// initialization ORDER depends on which package-level initializers gc's
// cmd/compile/internal/staticinit folds into the data section.
//
// THE MECHANISM (docs/BUGS.md BUG-061; docs/spec-divergence-ledger.md
// L-011). gc schedules only the packages with residual initialization
// WORK (inittask.go). "Residual" is what survives staticinit, and
// staticinit folds strictly more than go/types' constant folding: array,
// slice and struct literals of static elements, `&global`, copies of
// statically initialized globals, func values, `[]byte("lit")`,
// conversions to interface of static values and — with the inliner on —
// calls whose inlined body is a single `return <static>` (errors.New's
// shape). The frontend's rule (sourceHasInitWork) calls every
// non-constant initializer work, so it can keep a node gc deleted. A
// spurious node keeps a spurious EDGE, and an edge can delay an importer
// past a package it should have beaten: the pinned witness
// multipkg/init-order-staticinit (zq's `var A = [3]int{1, 2, 3}` holds la
// behind lb; gc 12, frontend 21).
//
// THE RULING. [USER] Mike 2026-10-12, release-readiness §5: «D1: I think
// this should probably be refused, if it's easy to exclude.» This file
// is the exclusion; the staticinit model (a decision at a point where gc
// is not single-valued — L-011) stays owed.
//
// THE RULE, in two parts, both legible:
//
//  1. CLASSIFY every package-level initializer of a source package into
//     three kinds (initializerKind): CONSTANT (go/types folded it —
//     pruned under both rules, as before); WORK (a shape StaticAssign
//     has no case for and the inliner cannot rescue: map literals,
//     arithmetic, indexing, field reads, receives, non-NOP conversions,
//     calls through interfaces or func values, calls to a body that is
//     not a single return, …); or MAYBE-STATIC (every other non-constant
//     shape — the ones staticinit may fold). A package is UNCERTAIN iff
//     it has no init function with a body, no WORK initializer, and at
//     least one MAYBE-STATIC one: the frontend schedules it, gc may not.
//     The emitted schedule is UNCHANGED by this file (an uncertain
//     package is still a node, exactly as before).
//
//  2. ENUMERATE. For every assignment of "has work" / "pruned" to the
//     uncertain packages, recompute gc's node set and walk the schedule;
//     the program is REFUSED iff some assignment orders the packages
//     that have work under it differently from the emitted schedule. A
//     package nobody imports, or one that is a node anyway because it
//     imports a node, can never move another package: those lower as
//     before. Only the sensitive shape refuses.
//
// THE DIRECTION, honestly. The classifier errs toward MAYBE-STATIC:
// WORK is claimed only where gc's code is read to have no static path
// (deps/go/src/cmd/compile/internal/staticinit/sched.go, StaticAssign +
// staticAssignInlinedCall; ir.StaticValue follows PAUTO names only, so
// no package-level receiver is devirtualized; the reader flattens
// explicit blocks and drops constant-false loops before the inliner
// sees a body). Over-classifying as MAYBE-STATIC can only add a refusal
// (never a silent wrong order); under-classifying would reintroduce the
// bug, so every WORK arm cites its gc case. The enumeration is exact
// for the classification it is given.

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/printer"
	"go/token"
	"go/types"
	"sort"
	"strings"
)

// exprSourceText renders an initializer as written, on one line, for
// the refusal message (types.ExprString elides composite literals to
// `{…}`, which hides the very shape the message is about).
func exprSourceText(fset *token.FileSet, e ast.Expr) string {
	var b strings.Builder
	if err := printer.Fprint(&b, fset, e); err != nil {
		return types.ExprString(e)
	}
	text := strings.Join(strings.Fields(b.String()), " ")
	const limit = 120
	if r := []rune(text); len(r) > limit {
		text = string(r[:limit]) + "…"
	}
	return text
}

func constantBoolValue(tv types.TypeAndValue) (bool, bool) {
	if tv.Value == nil || tv.Value.Kind() != constant.Bool {
		return false, false
	}
	return constant.BoolVal(tv.Value), true
}

// initializerKind is the classification of one package-level variable
// initializer against gc's staticinit.
type initializerKind int

const (
	// initConstant: go/types recorded a constant value. gc's fold is at
	// least as strong, so the initializer is never work (the rule
	// sourceHasInitWork already applied).
	initConstant initializerKind = iota
	// initMaybeStatic: not a constant, but of a shape staticinit MAY
	// write into the data section. Whether gc counts it as work is not
	// decided by the frontend.
	initMaybeStatic
	// initWork: a shape StaticAssign has no case for and inlining cannot
	// turn into one — certainly residual work under gc.
	initWork
)

// staticinitEnumCap bounds the enumeration: 2^cap schedules of a
// handful of nodes. A program with more uncertain packages than this
// refuses by name rather than guessing — the cap is a fail-closed
// budget, not a tuning knob.
const staticinitEnumCap = 12

// initSite is one MAYBE-STATIC initializer, for the refusal message.
type initSite struct {
	pkg  string // import path of the package
	text string // `var X = <expr>` as written
	pos  token.Position
}

func (s initSite) String() string {
	return fmt.Sprintf("%s at %s", s.text, s.pos)
}

// sourceInitWork classifies a SOURCE package's initialization work:
// certain reports whether gc certainly schedules it on its own account
// (an init function with a body, or a WORK initializer); maybe lists
// the MAYBE-STATIC initializers. The frontend's node fact is
// `certain || len(maybe) > 0` — sourceHasInitWork's rule, unchanged —
// and the package is UNCERTAIN iff !certain && len(maybe) > 0.
func (l *loader) sourceInitWork(u *sourcePkg) (certain bool, maybe []initSite) {
	for _, f := range u.files {
		for _, decl := range f.Decls {
			switch d := decl.(type) {
			case *ast.FuncDecl:
				// gc drops an init function whose body is empty
				// (pkginit/init.go MakeTask: "Skip init functions with
				// empty bodies"); any statement at all is work.
				if d.Recv == nil && d.Name.Name == "init" && d.Body != nil && len(d.Body.List) > 0 {
					certain = true
				}
			case *ast.GenDecl:
				if d.Tok != token.VAR {
					continue
				}
				for _, spec := range d.Specs {
					vs, ok := spec.(*ast.ValueSpec)
					if !ok {
						continue
					}
					if len(vs.Values) == 0 {
						continue // zero value: no initializer, no work
					}
					if len(vs.Names) != len(vs.Values) {
						// `var a, b = f()`: OAS2FUNC/OAS2MAPR/…; tryStaticInit
						// returns false for len(lhs) > 1 (the all-blank discard
						// needs a side-effect-free rhs, and a call is not).
						// A shape mismatch go/types accepted is a tuple.
						certain = true
						continue
					}
					for i, value := range vs.Values {
						blank := vs.Names[i].Name == "_"
						switch l.initializerKind(u, value, blank) {
						case initConstant:
						case initWork:
							certain = true
						case initMaybeStatic:
							maybe = append(maybe, initSite{
								pkg:  u.path,
								text: "var " + vs.Names[i].Name + " = " + exprSourceText(l.fset, value),
								pos:  l.fset.Position(vs.Names[i].Pos()),
							})
						}
					}
				}
			}
		}
	}
	return certain, maybe
}

// initializerKind classifies one initializer expression of package u.
// blank says the declared name is `_`: gc DISCARDS a blank assignment
// whose rhs has no side effects (tryStaticInit, allBlank && !AnySideEffects),
// so a blank WORK-shaped initializer without a call or receive is not
// certainly work — it is reported MAYBE-STATIC (the conservative slot;
// the emitted schedule keeps the package a node either way).
func (l *loader) initializerKind(u *sourcePkg, e ast.Expr, blank bool) initializerKind {
	k := l.exprInitKind(u, e)
	if blank && k == initWork && !l.mayHaveSideEffects(u, e) {
		return initMaybeStatic
	}
	return k
}

// exprInitKind is the classifier proper. Each WORK arm names the gc
// reading it rests on; everything not named is MAYBE-STATIC.
func (l *loader) exprInitKind(u *sourcePkg, e ast.Expr) initializerKind {
	tv, typed := u.info.Types[e]
	if !typed {
		// An expression go/types never typed should not exist after a
		// clean Check: fail towards a node, as sourceHasInitWork did —
		// and towards the enumeration, since "a node" is the frontend's
		// answer, not gc's.
		return initMaybeStatic
	}
	if tv.Value != nil {
		return initConstant
	}
	switch x := e.(type) {
	case *ast.ParenExpr:
		return l.exprInitKind(u, x.X)

	case *ast.Ident:
		switch obj := u.info.Uses[x].(type) {
		case *types.Nil:
			return initMaybeStatic // ONIL: static
		case *types.Func:
			return initMaybeStatic // PFUNC: staticcopy takes the func address
		case *types.Var:
			// ONAME → staticcopy: refused for a foreign package's variable
			// (rn.Sym().Pkg != types.LocalPkg) and for a STRING-typed one
			// (cmd/link -X may overwrite it, #34675); otherwise it depends
			// on the source variable's own initializer — not decided here.
			if obj.Pkg() != u.pkg || isStringType(obj.Type().Underlying()) {
				return initWork
			}
			return initMaybeStatic
		}
		return initWork

	case *ast.SelectorExpr:
		if sel, ok := u.info.Selections[x]; ok {
			switch sel.Kind() {
			case types.MethodExpr:
				return initMaybeStatic // OMETHEXPR: staticcopy of the wrapper's address
			case types.MethodVal:
				return initWork // OMETHVALUE: no StaticAssign case (a runtime closure)
			case types.FieldVal:
				return initWork // ODOT/ODOTPTR: no StaticAssign case
			}
			return initWork
		}
		// A qualified identifier: the same rules as a bare one, foreign.
		switch u.info.Uses[x.Sel].(type) {
		case *types.Func:
			return initMaybeStatic
		case *types.Var:
			return initWork // foreign PEXTERN: staticcopy refuses it
		}
		return initWork

	case *ast.FuncLit:
		// OCLOSURE without captured variables (nothing to capture at
		// package scope): assigned at link time.
		return initMaybeStatic

	case *ast.CompositeLit:
		if _, isMap := tv.Type.Underlying().(*types.Map); isMap {
			return initWork // OMAPLIT: StaticAssign breaks to `return false`
		}
		if p, isPtr := tv.Type.Underlying().(*types.Pointer); isPtr {
			// An elided `&T{…}` inside a []*T literal: the pointer literal
			// of a map is work like any map literal.
			if _, isMap := p.Elem().Underlying().(*types.Map); isMap {
				return initWork
			}
		}
		// OARRAYLIT/OSLICELIT/OSTRUCTLIT return true with each element
		// assigned through StaticAssign; a failing element is appended
		// as a dynamic statement, i.e. work.
		for _, elt := range x.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				elt = kv.Value
			}
			if l.exprInitKind(u, elt) == initWork {
				return initWork
			}
		}
		return initMaybeStatic

	case *ast.UnaryExpr:
		switch x.Op {
		case token.AND:
			if lit, ok := ast.Unparen(x.X).(*ast.CompositeLit); ok {
				return l.exprInitKind(u, lit) // OPTRLIT
			}
			if l.isStaticLoc(u, x.X) {
				return initMaybeStatic // OADDR of a StaticLoc
			}
			return initWork // OADDR falling through OPTRLIT's switch: no case
		case token.ARROW:
			return initWork // ORECV: no case
		}
		return initWork // ONEG/ONOT/OBITNOT/OPLUS of a non-constant: no case

	case *ast.BinaryExpr:
		return initWork // OADD … OOROR of non-constants: no case

	case *ast.CallExpr:
		return l.callInitKind(u, x, tv)

	case *ast.IndexExpr, *ast.IndexListExpr:
		// A generic function instantiation used as a value is a func
		// value; an element read is OINDEX, which has no case.
		if _, isSig := tv.Type.Underlying().(*types.Signature); isSig {
			return initMaybeStatic
		}
		return initWork

	case *ast.SliceExpr, *ast.TypeAssertExpr, *ast.StarExpr:
		return initWork // OSLICE*/ODOTTYPE/ODEREF: no case
	}
	// Anything unforeseen: a node under the frontend's rule, and not
	// claimed certain — the enumeration decides whether it matters.
	return initMaybeStatic
}

// callInitKind classifies a call expression: a conversion, a builtin, or
// a function/method call.
func (l *loader) callInitKind(u *sourcePkg, call *ast.CallExpr, tv types.TypeAndValue) initializerKind {
	funTV, ok := u.info.Types[call.Fun]
	if ok && funTV.IsType() {
		return l.conversionInitKind(u, call, tv.Type)
	}
	if ok && funTV.IsBuiltin() {
		// make/new/append/copy/len/cap/min/max/complex/real/imag/clear
		// and the unsafe family: none has a StaticAssign case (a
		// constant-valued builtin call was folded by go/types already).
		return initWork
	}
	fun := ast.Unparen(call.Fun)
	// A generic instantiation: the callee is the inner identifier.
	switch f := fun.(type) {
	case *ast.IndexExpr:
		fun = ast.Unparen(f.X)
	case *ast.IndexListExpr:
		fun = ast.Unparen(f.X)
	}
	var fn *types.Func
	switch f := fun.(type) {
	case *ast.Ident:
		fn, _ = u.info.Uses[f].(*types.Func)
	case *ast.SelectorExpr:
		if sel, ok := u.info.Selections[f]; ok {
			switch sel.Kind() {
			case types.MethodVal:
				if _, isIface := sel.Recv().Underlying().(*types.Interface); isIface {
					// OCALLINTER. ir.StaticValue follows PAUTO names only, so
					// a package-level receiver is never devirtualized — but a
					// receiver that is itself a conversion to the interface
					// (`I(T{}).M()`) is (devirtualize.StaticCall sees the
					// OCONVIFACE), and the devirtualized call may inline.
					if l.isConversionToInterface(u, ast.Unparen(f.X)) {
						return initMaybeStatic
					}
					return initWork
				}
				fn, _ = sel.Obj().(*types.Func)
			case types.MethodExpr:
				fn, _ = sel.Obj().(*types.Func)
			case types.FieldVal:
				return initWork // a call through a func-typed field: OCALLFUNC on a non-PFUNC
			}
		} else {
			fn, _ = u.info.Uses[f.Sel].(*types.Func)
		}
	}
	if fn == nil {
		// A call through a func value (a package-level variable, a call
		// result, a closure literal called in place): inlCallee needs a
		// PFUNC name or an OCLOSURE; a PEXTERN name is neither.
		if _, isLit := fun.(*ast.FuncLit); isLit {
			return initMaybeStatic // the inliner does inline a called closure literal
		}
		return initWork
	}
	if _, isIface := recvInterface(fn); isIface {
		// An interface method reached through a method expression value
		// (`I.M(x)`): the wrapper's body is a dynamic dispatch.
		return initWork
	}
	decl := l.funcDeclOf(fn)
	if decl == nil {
		// No source body (export data only, e.g. errors.New): gc may
		// inline it and fold the single return — not decided here.
		return initMaybeStatic
	}
	if decl.Body == nil {
		return initWork // body-less (assembly-backed): nothing to inline
	}
	if l.bodyIsSingleReturn(decl) {
		return initMaybeStatic // staticAssignInlinedCall's shape
	}
	return initWork // the inlined block is not DCL/AS2/GOTO: `len(list) != 3`
}

// conversionInitKind classifies T(x) for a type T. StaticAssign strips
// OCONVNOP, folds OSTR2BYTES of a literal and OCONVIFACE of a static
// operand, and has no case for the value-changing conversions.
func (l *loader) conversionInitKind(u *sourcePkg, call *ast.CallExpr, to types.Type) initializerKind {
	if len(call.Args) != 1 {
		return initMaybeStatic // not a shape go/types accepts; stay conservative
	}
	arg := call.Args[0]
	argTV, ok := u.info.Types[arg]
	if !ok {
		return initMaybeStatic
	}
	if _, isNil := u.info.Uses[identOf(arg)].(*types.Nil); isNil || (argTV.IsNil()) {
		return initMaybeStatic // (*T)(nil), I(nil): ONIL
	}
	if _, toIface := to.Underlying().(*types.Interface); toIface {
		// OCONVIFACE: an interface-typed operand is static only when nil
		// (`return val.Op() == ir.ONIL`); a concrete operand is static iff
		// the operand is.
		if _, fromIface := argTV.Type.Underlying().(*types.Interface); fromIface {
			return initWork
		}
		if l.exprInitKind(u, arg) == initWork {
			return initWork
		}
		return initMaybeStatic
	}
	from := argTV.Type.Underlying()
	toU := to.Underlying()
	if isStringType(from) {
		if argTV.Value != nil && isByteSlice(toU) {
			return initMaybeStatic // OSTR2BYTES of a literal
		}
		if isByteSlice(toU) || isRuneSlice(toU) {
			return initWork // OSTR2BYTES of a variable / OSTR2RUNES: no static path
		}
	}
	if isStringType(toU) && (isByteSlice(from) || isRuneSlice(from) || isIntegerType(from)) {
		return initWork // OBYTES2STR/ORUNES2STR/ORUNESTR: no case
	}
	if fb, ok := from.(*types.Basic); ok {
		if tb, ok := toU.(*types.Basic); ok && fb.Kind() != tb.Kind() {
			return initWork // OCONV between distinct basic kinds: no case
		}
	}
	// Everything else is OCONVNOP-shaped (same underlying representation):
	// the operand decides.
	return l.exprInitKind(u, arg)
}

// isConversionToInterface reports whether e is `I(x)` for an interface
// type I and a non-interface x — the receiver shape devirtualize.StaticCall
// rewrites.
func (l *loader) isConversionToInterface(u *sourcePkg, e ast.Expr) bool {
	call, ok := e.(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return false
	}
	funTV, ok := u.info.Types[call.Fun]
	if !ok || !funTV.IsType() {
		return false
	}
	if _, toIface := funTV.Type.Underlying().(*types.Interface); !toIface {
		return false
	}
	argTV, ok := u.info.Types[call.Args[0]]
	if !ok {
		return false
	}
	_, fromIface := argTV.Type.Underlying().(*types.Interface)
	return !fromIface
}

// isStaticLoc mirrors staticinit.StaticLoc: a package-level name, a
// field of one through value selectors (ODOT, never ODOTPTR), or an
// array element at a constant index.
func (l *loader) isStaticLoc(u *sourcePkg, e ast.Expr) bool {
	switch x := ast.Unparen(e).(type) {
	case *ast.Ident:
		v, ok := u.info.Uses[x].(*types.Var)
		return ok && v.Parent() == v.Pkg().Scope()
	case *ast.SelectorExpr:
		if sel, ok := u.info.Selections[x]; ok {
			return sel.Kind() == types.FieldVal && !sel.Indirect() && l.isStaticLoc(u, x.X)
		}
		v, ok := u.info.Uses[x.Sel].(*types.Var)
		return ok && v.Parent() == v.Pkg().Scope()
	case *ast.IndexExpr:
		xt, ok := u.info.Types[x.X]
		if !ok {
			return false
		}
		if _, isArray := xt.Type.Underlying().(*types.Array); !isArray {
			return false
		}
		it, ok := u.info.Types[x.Index]
		return ok && it.Value != nil && l.isStaticLoc(u, x.X)
	}
	return false
}

// mayHaveSideEffects is the conservative twin of staticinit.AnySideEffects
// for the blank-discard rule: a call that is not a conversion or a
// side-effect-free builtin, or a receive, may have effects. Everything
// else in isSideEffect's no-effect list is syntax-only.
func (l *loader) mayHaveSideEffects(u *sourcePkg, e ast.Expr) bool {
	found := false
	ast.Inspect(e, func(n ast.Node) bool {
		if found {
			return false
		}
		switch x := n.(type) {
		case *ast.CallExpr:
			if tv, ok := u.info.Types[x.Fun]; ok {
				if tv.IsType() {
					return true // a conversion: look inside
				}
				if tv.IsBuiltin() {
					switch identOf(x.Fun).Name {
					case "len", "cap", "new", "real", "imag", "complex":
						return true // isSideEffect: false
					}
				}
			}
			found = true
			return false
		case *ast.UnaryExpr:
			if x.Op == token.ARROW {
				found = true
				return false
			}
		case *ast.FuncLit:
			return false // a body is not evaluated
		}
		return true
	})
	return found
}

// bodyIsSingleReturn reports whether the function body the inliner would
// see is exactly one `return <one value>` — staticAssignInlinedCall's
// DCL/AS2/GOTO shape. The reader flattens explicit blocks, drops empty
// statements and constant-false `for`s (keeping their init), and folds
// a constant-condition `if` into its live branch; the count here does
// the same, erring toward "single" (toward MAYBE-STATIC).
func (l *loader) bodyIsSingleReturn(decl *ast.FuncDecl) bool {
	var live []ast.Stmt
	var flatten func(list []ast.Stmt)
	flatten = func(list []ast.Stmt) {
		for _, s := range list {
			switch st := s.(type) {
			case *ast.EmptyStmt:
			case *ast.BlockStmt:
				flatten(st.List)
			case *ast.ForStmt:
				if st.Cond != nil && l.constBool(decl, st.Cond) == constFalse {
					if st.Init != nil {
						flatten([]ast.Stmt{st.Init})
					}
					continue
				}
				live = append(live, st)
			case *ast.IfStmt:
				switch l.constBool(decl, st.Cond) {
				case constTrue:
					if st.Init != nil {
						flatten([]ast.Stmt{st.Init})
					}
					flatten(st.Body.List)
				case constFalse:
					if st.Init != nil {
						flatten([]ast.Stmt{st.Init})
					}
					if st.Else != nil {
						flatten([]ast.Stmt{st.Else})
					}
				default:
					live = append(live, st)
				}
			default:
				live = append(live, st)
			}
		}
	}
	flatten(decl.Body.List)
	if len(live) != 1 {
		return false
	}
	ret, ok := live[0].(*ast.ReturnStmt)
	if !ok {
		return false
	}
	// One result is the shape; a bare `return` with named results is
	// left to the conservative side.
	return len(ret.Results) <= 1
}

type constBoolean int

const (
	constUnknown constBoolean = iota
	constTrue
	constFalse
)

// constBool reads a condition's constant value from whichever unit
// declares the function.
func (l *loader) constBool(decl *ast.FuncDecl, cond ast.Expr) constBoolean {
	info := l.infoOfDecl(decl)
	if info == nil {
		return constUnknown
	}
	tv, ok := info.Types[cond]
	if !ok || tv.Value == nil {
		return constUnknown
	}
	if b, ok := constantBoolValue(tv); ok {
		if b {
			return constTrue
		}
		return constFalse
	}
	return constUnknown
}

// funcDeclOf finds the declaration of fn among every source unit of the
// program (local packages, library units, main). Nil for an export-data
// callee. The index is built once, on first use.
func (l *loader) funcDeclOf(fn *types.Func) *ast.FuncDecl {
	if l.funcDecls == nil {
		l.funcDecls = map[*types.Func]*ast.FuncDecl{}
		l.declInfo = map[*ast.FuncDecl]*types.Info{}
		for _, u := range l.allUnits() {
			if u.info == nil {
				continue
			}
			for _, f := range u.files {
				for _, d := range f.Decls {
					fd, ok := d.(*ast.FuncDecl)
					if !ok {
						continue
					}
					if obj, ok := u.info.Defs[fd.Name].(*types.Func); ok && obj != nil {
						l.funcDecls[obj] = fd
						l.declInfo[fd] = u.info
					}
				}
			}
		}
	}
	return l.funcDecls[fn.Origin()]
}

func (l *loader) infoOfDecl(decl *ast.FuncDecl) *types.Info {
	return l.declInfo[decl]
}

// allUnits lists the loader's source units (locals and libraries) plus
// the main unit once it is registered (specInitOrder runs after
// type-checking, when every unit has its info).
func (l *loader) allUnits() []*sourcePkg {
	out := make([]*sourcePkg, 0, len(l.locals)+1)
	for _, u := range l.locals {
		out = append(out, u)
	}
	if l.mainUnit != nil {
		out = append(out, l.mainUnit)
	}
	return out
}

func recvInterface(fn *types.Func) (*types.Interface, bool) {
	sig, ok := fn.Type().(*types.Signature)
	if !ok || sig.Recv() == nil {
		return nil, false
	}
	iface, ok := sig.Recv().Type().Underlying().(*types.Interface)
	return iface, ok
}

func identOf(e ast.Expr) *ast.Ident {
	switch x := ast.Unparen(e).(type) {
	case *ast.Ident:
		return x
	case *ast.SelectorExpr:
		return x.Sel
	}
	return &ast.Ident{}
}

// isIntegerType reports whether an underlying type is an integer kind
// (isStringType / isByteSlice / isRuneSlice are emit.go's; all four take
// an UNDERLYING type).
func isIntegerType(t types.Type) bool {
	b, ok := t.(*types.Basic)
	return ok && b.Info()&types.IsInteger != 0
}

// ---- the enumeration ----

// checkStaticinitSensitivity refuses the program iff the order of the
// packages WITH work depends on which uncertain packages gc prunes.
// keys is the schedule's sorted key set; emitted is the walk under the
// frontend's rule (every uncertain package a node).
func (l *loader) checkStaticinitSensitivity(g *initGraph, keys []string, emitted []string) error {
	uncertain := []string{}
	for prefix, sites := range g.uncertain {
		if len(sites) > 0 {
			uncertain = append(uncertain, prefix)
		}
	}
	if len(uncertain) == 0 {
		return nil
	}
	sort.Strings(uncertain)
	if len(uncertain) > staticinitEnumCap {
		return unsup("the program initialization order is not decided by the frontend's pruning rule (BUG-061): %d packages have only initializers gc's staticinit may fold into the data section (%s), more than the %d the sensitivity check enumerates — refused by name rather than guessed",
			len(uncertain), strings.Join(uncertain, ", "), staticinitEnumCap)
	}
	for mask := 0; mask < 1<<len(uncertain); mask++ {
		if mask == 1<<len(uncertain)-1 {
			continue // every uncertain package has work: the emitted assumption
		}
		work := map[string]bool{}
		for p, w := range g.work {
			work[p] = w
		}
		pruned := []string{}
		for i, p := range uncertain {
			if mask&(1<<i) == 0 {
				work[p] = false
				pruned = append(pruned, p)
			}
		}
		node := solveInitNodes(g, work)
		order, err := walkInitSchedule(keys, g, node)
		if err != nil {
			return err
		}
		observable := func(walk []string) []string {
			out := []string{}
			for _, p := range walk {
				if _, isSrc := g.src[p]; isSrc && work[p] {
					out = append(out, p)
				}
			}
			return out
		}
		have, want := observable(emitted), observable(order)
		if !equalStrings(have, want) {
			sites := []string{}
			for _, p := range pruned {
				for _, s := range g.uncertain[p] {
					sites = append(sites, s.String())
				}
			}
			return unsup("the program initialization order is not decided by the frontend's pruning rule (BUG-061): package(s) %s have no certain initialization work — the initializer(s) %s are non-constant but of a shape cmd/compile/internal/staticinit may fold into the data section, so whether gc schedules them is not decided syntactically, and the order of the packages WITH work depends on the answer: scheduled %v, pruned %v — refused by name (the staticinit model is owed: docs/BUGS.md BUG-061, docs/spec-divergence-ledger.md L-011)",
				strings.Join(pruned, ", "), strings.Join(sites, "; "), have, want)
		}
	}
	return nil
}

func equalStrings(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}
