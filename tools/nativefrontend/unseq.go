package main

// unseq.go — Stage C of the evaluation-order model v2.1 (lane
// core/unseq-stage-c-0919; design docs/2026-09-16_evaluation-order-model-v2.md
// §3.1/§3.7, review §2 row C; the Stage C rulings [USER] Mike 2026-09-19,
// relayed: width of P = all mutable reads STAGED — this pilot carries the
// minimal P(ii) reads its fixtures need; N1 SPLIT; N3 REFUSE).
//
// THE WHOLE-SWEEP MIGRATION BOUNDARY, as the emitter's decision procedure.
// One statement's evaluation phase (a SWEEP: a block-level statement in
// emitStmtList) is lowered EITHER as ONE `unseq` graph (Stmt.unseq, the
// Stage B construct) OR by the legacy E13 probe path (unseq-probe / ANF
// hoists) — never a mixture, never by fixture name. The decision is
// SYNTACTIC over the typed AST and is the ONE function `unseqClassify`:
//
//   admitted  :=  statement form ∈ pilot forms
//              ∧  every operand expression ∈ pilot expression grammar
//              ∧  calls ≥ 1  ∧  nonEvents ≥ 1
//
// where `calls` counts the CALL occurrences the sweep would carry (a call
// to a same-package top-level function, a call through a func-typed
// local, an immediately-invoked func literal — the events with EFFECTS;
// a non-constant len/cap is an E1-ordered event occurrence inside an
// admitted sweep but, having no effect and no failure on a slice value,
// does not admit one) and `nonEvents` counts the occurrences that can be observed
// AGAINST an event (a read of an address-taken local — the pilot's P(ii)
// reads; a slice-element checked access; a failing pure op — slice
// expression, type assertion, division/remainder by a non-constant,
// a shift by a non-constant signed count; a slice-element target plan;
// a compound target's load of an address-taken local; a `&&`/`||`
// guard). A sweep with no event, or with an event but no occurrence
// that could be reordered against it, has no spec-unsequenced pair the
// pilot envelopes and stays on the legacy path (E12(ii)'s read-vs-read
// axis widens at Stage E). Everything the grammar does not name —
// globals, pointers, fields, maps, arrays, strings indexing, methods,
// receives, sends, conversions, allocations, `recover`, multi-target
// assignment, blank targets, sub-accumulator sweeps (if/for/switch
// heads) — sends the WHOLE sweep to the legacy path, by name.
//
// The classifier has no emission side effects (it lifts no func literal,
// hoists nothing), so `--unseq-census` (main.go) runs it over every
// statement list of a program and prints one TSV row per sweep; the
// emitter (Stage C2) consults the same function before lowering.

import (
	"go/ast"
	"go/token"
	"go/types"
	"os"
)

// unseqCtx is what the classifier needs of the enclosing function: its
// body (for the address-taken analysis), the set of variables reached
// through a capture pointer inside a lifted body (their reads are `*p`
// derefs, outside the pilot), and the function's result tuple (for
// `return`).
type unseqCtx struct {
	body     *ast.BlockStmt
	captured map[types.Object]bool
	results  *types.Tuple
}

// unseqDecision is one sweep's verdict and census row.
type unseqDecision struct {
	admitted  bool
	form      string // define | assign | elem-assign | compound | incdec | return | call-stmt | print-stmt | other
	reason    string // the FIRST construct outside the grammar ("" when every operand is inside it)
	events    int    // every invocation-kind occurrence: calls AND non-constant len/cap (E1-ordered)
	calls     int    // the CALLS among them — the events with effects; the trigger counts these
	nonEvents int
}

// unseqLocalVar reports whether obj is a function-local variable (a
// parameter, a named result or a body local) — never a field, never a
// package-level variable of any source unit.
func (e *emitter) unseqLocalVar(obj types.Object) (*types.Var, bool) {
	v, ok := obj.(*types.Var)
	if !ok || v.IsField() {
		return nil, false
	}
	if v.Parent() == nil || e.isSourceScope(v.Parent()) {
		return nil, false
	}
	return v, true
}

// unseqTypeOK is the pilot's TYPE grammar: integer kinds, bool, string
// (never untyped, never unsafe.Pointer), slices of admitted types, and
// the empty interface (`any` / `interface{}`, the type-assertion
// operand). Aliases are transparent. Named types, pointers, arrays,
// maps, structs, channels, funcs (except in callee position), floats and
// complex are outside.
func unseqTypeOK(t types.Type) bool {
	if t == nil {
		return false
	}
	switch u := types.Unalias(t).(type) {
	case *types.Basic:
		if u.Info()&types.IsUntyped != 0 {
			return false
		}
		return u.Info()&(types.IsInteger|types.IsBoolean|types.IsString) != 0
	case *types.Slice:
		return unseqTypeOK(u.Elem())
	case *types.Interface:
		return u.Empty()
	}
	return false
}

// unseqConstTypeOK admits a CONSTANT operand: an integer/bool/string
// constant, typed or untyped (go/types records the converted type at
// every use the machine needs; `emitConstValue` renders both).
func unseqConstTypeOK(t types.Type) bool {
	if t == nil {
		return false
	}
	b, ok := types.Unalias(t).Underlying().(*types.Basic)
	if !ok {
		return false
	}
	return b.Info()&(types.IsInteger|types.IsBoolean|types.IsString) != 0
}

// unseqRootIdent strips parentheses, index, slice and selector steps to
// the variable an addressing chain is rooted at (`&a[i].f` roots at `a`).
func unseqRootIdent(x ast.Expr) *ast.Ident {
	for {
		switch v := x.(type) {
		case *ast.ParenExpr:
			x = v.X
		case *ast.IndexExpr:
			x = v.X
		case *ast.SliceExpr:
			x = v.X
		case *ast.SelectorExpr:
			x = v.X
		case *ast.StarExpr:
			return nil // through a pointer: the pointee, not a local
		case *ast.Ident:
			return v
		default:
			return nil
		}
	}
}

// unseqAddrTaken computes (and caches per body) the set of the function's
// local variables whose ADDRESS is taken anywhere in its body: captured by
// a func literal (the lifted literal receives `&v`), the operand root of
// an explicit `&`, the base of a slicing of an array variable, or the
// receiver operand of a method call (a pointer receiver takes `&v`
// implicitly; recorded conservatively for every method call). A local
// outside this set is PRIVATE — order-transparent (v2.1 §1: «A private
// local … and a constant are order-transparent: not occurrences»); a
// local inside it is a mutable location whose read is a READ occurrence
// (the pilot's P(ii) reads — the W1/W6/R1/R6 witnesses' `a`, `x`, `x`/`y`,
// `a`).
func (e *emitter) unseqAddrTaken(body *ast.BlockStmt) map[types.Object]bool {
	if body == nil {
		return map[types.Object]bool{}
	}
	if e.unseqAddr == nil {
		e.unseqAddr = map[*ast.BlockStmt]map[types.Object]bool{}
	}
	if cached, ok := e.unseqAddr[body]; ok {
		return cached
	}
	taken := map[types.Object]bool{}
	mark := func(id *ast.Ident) {
		if id == nil {
			return
		}
		if obj := e.info.Uses[id]; obj != nil {
			taken[obj] = true
		} else if obj := e.info.Defs[id]; obj != nil {
			taken[obj] = true
		}
	}
	ast.Inspect(body, func(n ast.Node) bool {
		switch v := n.(type) {
		case *ast.FuncLit:
			for _, c := range e.freeCaptures(v) {
				taken[c] = true
			}
		case *ast.UnaryExpr:
			if v.Op == token.AND {
				mark(unseqRootIdent(v.X))
			}
		case *ast.SliceExpr:
			if t := e.goTypeOf(v.X); t != nil {
				if _, isArr := types.Unalias(t).Underlying().(*types.Array); isArr {
					mark(unseqRootIdent(v.X))
				}
			}
		case *ast.CallExpr:
			if sel, ok := ast.Unparen(v.Fun).(*ast.SelectorExpr); ok {
				if s, isSel := e.info.Selections[sel]; isSel && s.Kind() == types.MethodVal {
					mark(unseqRootIdent(sel.X))
				}
			}
		}
		return true
	})
	e.unseqAddr[body] = taken
	return taken
}

// unseqExprKind is the classifier's view of one operand.
type unseqExprKind int

const (
	unseqConst unseqExprKind = iota // a constant: an atom
	unseqAtom                       // a private local: an admitted stable read, an atom
	unseqValue                      // a produced VALUE (one or more occurrences)
)

// unseqExpr classifies an operand expression: whether it lies inside the
// pilot expression grammar (reason names the first construct outside it),
// what it lowers to, and how many event / non-event occurrences it
// carries. `valuePos` is true where a value is required (false only for
// the callee-position and statement-position calls handled by callers).
func (e *emitter) unseqExpr(x ast.Expr, ctx *unseqCtx, d *unseqDecision) (unseqExprKind, bool) {
	refuse := func(why string) (unseqExprKind, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return unseqConst, false
	}
	// A constant-folded node has no run-time evaluation.
	if tv, ok := e.typesEntry(x); ok && tv.Value != nil {
		if !unseqConstTypeOK(tv.Type) {
			return refuse("constant of a type outside the pilot grammar")
		}
		return unseqConst, true
	}
	switch v := x.(type) {
	case *ast.ParenExpr:
		return e.unseqExpr(v.X, ctx, d)
	case *ast.Ident:
		obj := e.info.Uses[v]
		if obj == nil {
			return refuse("unresolved identifier")
		}
		if _, isNil := obj.(*types.Nil); isNil {
			return refuse("nil")
		}
		if _, isFn := obj.(*types.Func); isFn {
			return refuse("function used as a value")
		}
		loc, isLocal := e.unseqLocalVar(obj)
		if !isLocal {
			if _, isPkg := e.isPackageVar(obj); isPkg {
				return refuse("package-level variable")
			}
			return refuse("non-local identifier")
		}
		if ctx.captured[obj] {
			return refuse("captured variable read through its pointer parameter (lifted body)")
		}
		if !unseqTypeOK(loc.Type()) {
			return refuse("local of a type outside the pilot grammar (" + loc.Type().String() + ")")
		}
		if e.unseqAddrTaken(ctx.body)[obj] {
			d.nonEvents++ // a mutable read: the pilot's P(ii) read
			return unseqValue, true
		}
		return unseqAtom, true
	case *ast.IndexExpr:
		bt := e.goTypeOf(v.X)
		if bt == nil {
			return refuse("index of an untyped base")
		}
		sl, isSlice := types.Unalias(bt).Underlying().(*types.Slice)
		if !isSlice {
			return refuse("index of a non-slice base (" + bt.String() + ")")
		}
		if !unseqTypeOK(sl.Elem()) {
			return refuse("slice element type outside the pilot grammar (" + sl.Elem().String() + ")")
		}
		if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
			return unseqConst, false
		}
		if _, ok := e.unseqExpr(v.Index, ctx, d); !ok {
			return unseqConst, false
		}
		d.nonEvents++ // the ONE checked access (N1 SPLIT: base/index are producers)
		return unseqValue, true
	case *ast.SliceExpr:
		bt := e.goTypeOf(v.X)
		if bt == nil {
			return refuse("slice of an untyped base")
		}
		if _, isSlice := types.Unalias(bt).Underlying().(*types.Slice); !isSlice {
			return refuse("slice expression on a non-slice base (" + bt.String() + ")")
		}
		if !unseqTypeOK(bt) {
			return refuse("slice type outside the pilot grammar (" + bt.String() + ")")
		}
		if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
			return unseqConst, false
		}
		for _, bound := range []ast.Expr{v.Low, v.High, v.Max} {
			if bound == nil {
				continue
			}
			if _, ok := e.unseqExpr(bound, ctx, d); !ok {
				return unseqConst, false
			}
		}
		d.nonEvents++ // a failing pure op (slice bounds)
		return unseqValue, true
	case *ast.CallExpr:
		if _, ok := e.unseqCall(v, ctx, d, 1); !ok {
			return unseqConst, false
		}
		return unseqValue, true
	case *ast.BinaryExpr:
		op, ok := binaryOp(v.Op)
		if !ok {
			return refuse("binary operator " + v.Op.String())
		}
		if op == "&&" || op == "||" {
			if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
				return unseqConst, false
			}
			if _, ok := e.unseqExpr(v.Y, ctx, d); !ok {
				return unseqConst, false
			}
			d.nonEvents++ // the guard entry + completion
			return unseqValue, true
		}
		xt := e.goTypeOf(v.X)
		if xt == nil || !unseqTypeOK(xt) {
			return refuse("binary operand type outside the pilot grammar")
		}
		if isComparison(op) {
			if _, isIface := types.Unalias(xt).Underlying().(*types.Interface); isIface {
				return refuse("interface comparison (may panic; outside the pilot)")
			}
		}
		if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
			return unseqConst, false
		}
		if _, ok := e.unseqExpr(v.Y, ctx, d); !ok {
			return unseqConst, false
		}
		if e.unseqBinaryMayFail(v) {
			d.nonEvents++ // division/remainder by a non-constant, shift by a non-constant signed count
		}
		return unseqValue, true
	case *ast.UnaryExpr:
		switch v.Op {
		case token.SUB, token.XOR, token.NOT:
		default:
			return refuse("unary operator " + v.Op.String())
		}
		if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
			return unseqConst, false
		}
		return unseqValue, true
	case *ast.TypeAssertExpr:
		if v.Type == nil {
			return refuse("type switch guard")
		}
		if _, isTup := e.goTypeOf(v).(*types.Tuple); isTup {
			return refuse("comma-ok type assertion in expression position")
		}
		ot := e.goTypeOf(v.X)
		if ot == nil || !unseqTypeOK(ot) {
			return refuse("type assertion on an operand type outside the pilot grammar")
		}
		if !unseqTypeOK(e.goTypeOf(v.Type)) {
			return refuse("type assertion to a type outside the pilot grammar")
		}
		if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
			return unseqConst, false
		}
		d.nonEvents++ // a failing pure op (spec#Type_assertions)
		return unseqValue, true
	case *ast.FuncLit:
		return refuse("func literal in value position")
	case *ast.StarExpr:
		return refuse("pointer indirection")
	case *ast.SelectorExpr:
		return refuse("selector (field / method / qualified name)")
	case *ast.CompositeLit:
		return refuse("composite literal")
	}
	return refuse("expression outside the pilot grammar")
}

// unseqBinaryMayFail: integer `/` or `%` by a non-constant divisor, or a
// shift by a non-constant SIGNED count (probeKind's census, narrowed to
// the pilot's integer types).
func (e *emitter) unseqBinaryMayFail(b *ast.BinaryExpr) bool {
	switch b.Op {
	case token.QUO, token.REM:
		if tv, ok := e.info.Types[b.Y]; ok && tv.Value != nil {
			return false
		}
		return true
	case token.SHL, token.SHR:
		if tv, ok := e.info.Types[b.Y]; ok && tv.Value != nil {
			return false
		}
		t := e.goTypeOf(b.Y)
		if t == nil {
			return true
		}
		basic, isBasic := types.Unalias(t).Underlying().(*types.Basic)
		return !isBasic || basic.Info()&types.IsUnsigned == 0
	}
	return false
}

// unseqCallee classifies a call's callee: a same-package, non-generic,
// non-variadic top-level function; a func-typed local (private or
// address-taken); or a func literal (lifted at lowering). Returns the
// signature.
func (e *emitter) unseqCallee(c *ast.CallExpr, ctx *unseqCtx, d *unseqDecision) (*types.Signature, bool) {
	refuse := func(why string) (*types.Signature, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return nil, false
	}
	if tv, ok := e.info.Types[c.Fun]; ok && tv.IsType() {
		return refuse("conversion")
	}
	switch fn := ast.Unparen(c.Fun).(type) {
	case *ast.Ident:
		switch obj := e.info.Uses[fn].(type) {
		case *types.Func:
			sig, _ := obj.Type().(*types.Signature)
			if sig == nil || sig.Recv() != nil {
				return refuse("method value callee")
			}
			if sig.TypeParams().Len() > 0 || sig.RecvTypeParams().Len() > 0 {
				return refuse("generic function callee")
			}
			if obj.Pkg() == nil || !e.isMainPackage(obj.Pkg()) {
				return refuse("callee outside the main package")
			}
			if _, isShim := shimRuntimeRefusalReasons[obj.Name()]; isShim {
				return refuse("shim runtime-refusal helper callee")
			}
			return sig, true
		case *types.Var:
			loc, isLocal := e.unseqLocalVar(obj)
			if !isLocal {
				return refuse("call through a non-local func value")
			}
			if ctx.captured[obj] {
				return refuse("call through a captured func variable (lifted body)")
			}
			sig, ok := types.Unalias(loc.Type()).Underlying().(*types.Signature)
			if !ok {
				return refuse("call through a non-func local")
			}
			if e.unseqAddrTaken(ctx.body)[obj] {
				d.nonEvents++ // the callee VALUE is a mutable read
			}
			return sig, true
		case *types.Builtin:
			return refuse("builtin " + fn.Name)
		}
		return refuse("callee kind")
	case *ast.FuncLit:
		sig, ok := e.goTypeOf(fn).(*types.Signature)
		if !ok {
			return refuse("func literal without a signature")
		}
		return sig, true
	}
	return refuse("callee expression outside the pilot grammar")
}

// unseqCall classifies a call: callee, arguments (atoms or values, no
// tuple forwarding, no variadic packing), result count ≤ maxResults (and
// ≥ 1 in value position: maxResults 1; a statement-position call passes
// 2 and may have none; `return f()` passes the result count it needs).
// A non-constant `len`/`cap` of a slice is the other event kind.
func (e *emitter) unseqCall(c *ast.CallExpr, ctx *unseqCtx, d *unseqDecision, maxResults int) (int, bool) {
	refuse := func(why string) (int, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return 0, false
	}
	if id, ok := ast.Unparen(c.Fun).(*ast.Ident); ok {
		if _, isBuiltin := e.info.Uses[id].(*types.Builtin); isBuiltin {
			switch id.Name {
			case "len", "cap":
				if len(c.Args) != 1 {
					return refuse(id.Name + " arity")
				}
				at := e.goTypeOf(c.Args[0])
				if at == nil {
					return refuse(id.Name + " of an untyped operand")
				}
				if _, isSlice := types.Unalias(at).Underlying().(*types.Slice); !isSlice {
					return refuse(id.Name + " of a non-slice operand (" + at.String() + ")")
				}
				if !unseqTypeOK(at) {
					return refuse(id.Name + " operand type outside the pilot grammar")
				}
				if _, ok := e.unseqExpr(c.Args[0], ctx, d); !ok {
					return 0, false
				}
				// spec#Built-in_functions «called like any other function»: an
				// E1-ordered event INSIDE an admitted sweep (BUG-062's forced
				// order against calls) — but it has no effect and cannot fail
				// on a slice value, so a read reordered against it is
				// unobservable: it does not by itself admit a sweep (`calls`).
				d.events++
				return 1, true
			}
			return refuse("builtin " + id.Name)
		}
	}
	sig, ok := e.unseqCallee(c, ctx, d)
	if !ok {
		return 0, false
	}
	if sig.Variadic() {
		return refuse("variadic callee")
	}
	if c.Ellipsis != token.NoPos {
		return refuse("spread argument")
	}
	if len(c.Args) != sig.Params().Len() {
		return refuse("argument arity (tuple forwarding)")
	}
	for i, a := range c.Args {
		if _, isTup := e.goTypeOf(a).(*types.Tuple); isTup {
			return refuse("multi-value argument")
		}
		pt := sig.Params().At(i).Type()
		if !unseqTypeOK(pt) {
			return refuse("parameter type outside the pilot grammar (" + pt.String() + ")")
		}
		if _, ok := e.unseqExpr(a, ctx, d); !ok {
			return 0, false
		}
	}
	n := sig.Results().Len()
	if n > 2 {
		return refuse("more than two results")
	}
	if n > maxResults {
		return refuse("result count outside this position")
	}
	if maxResults == 1 && n == 0 {
		return refuse("zero-result call in value position")
	}
	for i := 0; i < n; i++ {
		if !unseqTypeOK(sig.Results().At(i).Type()) {
			return refuse("result type outside the pilot grammar (" + sig.Results().At(i).Type().String() + ")")
		}
	}
	d.events++
	d.calls++
	return n, true
}

// unseqLocalTarget classifies an assignment target that is a plain local
// identifier: a local variable (not blank, not a package variable, not a
// captured variable inside a lifted body) of an admitted type. `define`
// selects Defs (a fresh `:=` declaration) over Uses.
func (e *emitter) unseqLocalTarget(id *ast.Ident, define bool, ctx *unseqCtx, d *unseqDecision) (*types.Var, bool) {
	refuse := func(why string) (*types.Var, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return nil, false
	}
	if id.Name == "_" {
		return refuse("blank target")
	}
	var obj types.Object
	if define {
		obj = e.info.Defs[id]
		if obj == nil {
			return refuse("define target is not a fresh declaration")
		}
	} else {
		obj = e.info.Uses[id]
	}
	if obj == nil {
		return refuse("unresolved target")
	}
	loc, isLocal := e.unseqLocalVar(obj)
	if !isLocal {
		return refuse("non-local target")
	}
	if ctx.captured[obj] {
		return refuse("captured target written through its pointer parameter (lifted body)")
	}
	if !unseqTypeOK(loc.Type()) {
		return refuse("target type outside the pilot grammar (" + loc.Type().String() + ")")
	}
	return loc, true
}

// unseqElemTarget classifies a slice-element target `a[i]`: base and index
// inside the grammar; the target PLAN is a non-event occurrence (frozen
// header + index, one identity for the load and the store — v2.1 §3.4).
func (e *emitter) unseqElemTarget(ix *ast.IndexExpr, ctx *unseqCtx, d *unseqDecision) bool {
	refuse := func(why string) bool {
		if d.reason == "" {
			d.reason = why
		}
		return false
	}
	bt := e.goTypeOf(ix.X)
	if bt == nil {
		return refuse("element target on an untyped base")
	}
	sl, isSlice := types.Unalias(bt).Underlying().(*types.Slice)
	if !isSlice {
		return refuse("element target on a non-slice base (" + bt.String() + ")")
	}
	if !unseqTypeOK(sl.Elem()) {
		return refuse("element target type outside the pilot grammar (" + sl.Elem().String() + ")")
	}
	if _, ok := e.unseqExpr(ix.X, ctx, d); !ok {
		return false
	}
	if _, ok := e.unseqExpr(ix.Index, ctx, d); !ok {
		return false
	}
	d.nonEvents++ // the target plan (and, for a compound target, its load)
	return true
}

// unseqClassify is THE whole-sweep decision procedure (header comment).
// It never emits: the census and the emitter call it alike.
func (e *emitter) unseqClassify(s ast.Stmt, ctx *unseqCtx) unseqDecision {
	d := unseqDecision{form: "other"}
	refuse := func(why string) unseqDecision {
		if d.reason == "" {
			d.reason = why
		}
		d.admitted = false
		return d
	}
	switch st := s.(type) {
	case *ast.AssignStmt:
		if len(st.Lhs) != 1 || len(st.Rhs) != 1 {
			d.form = "assign"
			return refuse("multi-target or tuple assignment")
		}
		if _, isTup := e.goTypeOf(st.Rhs[0]).(*types.Tuple); isTup {
			d.form = "assign"
			return refuse("multi-value right-hand side")
		}
		switch st.Tok {
		case token.DEFINE, token.ASSIGN:
			define := st.Tok == token.DEFINE
			if define {
				d.form = "define"
			} else {
				d.form = "assign"
			}
			switch l := ast.Unparen(st.Lhs[0]).(type) {
			case *ast.Ident:
				if _, ok := e.unseqLocalTarget(l, define, ctx, &d); !ok {
					return refuse("target")
				}
			case *ast.IndexExpr:
				if define {
					return refuse("define with an index target")
				}
				d.form = "elem-assign"
				if !e.unseqElemTarget(l, ctx, &d) {
					return refuse("target")
				}
			default:
				return refuse("assignment target outside the pilot grammar")
			}
			if _, ok := e.unseqExpr(st.Rhs[0], ctx, &d); !ok {
				return refuse("right-hand side")
			}
		default:
			d.form = "compound"
			op, ok := compoundOp(st.Tok)
			if !ok {
				return refuse("assignment operator " + st.Tok.String())
			}
			if !e.unseqReadWriteTarget(st.Lhs[0], ctx, &d) {
				return refuse("compound target")
			}
			if _, ok := e.unseqExpr(st.Rhs[0], ctx, &d); !ok {
				return refuse("right-hand side")
			}
			if op == "/" || op == "%" {
				if tv, ok := e.info.Types[st.Rhs[0]]; !ok || tv.Value == nil {
					d.nonEvents++ // the compound op itself may fail
				}
			}
			if op == "<<" || op == ">>" {
				if tv, ok := e.info.Types[st.Rhs[0]]; !ok || tv.Value == nil {
					if t := e.goTypeOf(st.Rhs[0]); t != nil {
						if b, isB := types.Unalias(t).Underlying().(*types.Basic); !isB || b.Info()&types.IsUnsigned == 0 {
							d.nonEvents++
						}
					}
				}
			}
		}
	case *ast.IncDecStmt:
		d.form = "incdec"
		if !e.unseqReadWriteTarget(st.X, ctx, &d) {
			return refuse("incdec target")
		}
	case *ast.ReturnStmt:
		d.form = "return"
		if len(st.Results) == 0 {
			return refuse("bare return")
		}
		if len(st.Results) == 1 {
			if call, isCall := ast.Unparen(st.Results[0]).(*ast.CallExpr); isCall {
				if tup, isTup := e.goTypeOf(call).(*types.Tuple); isTup {
					if ctx.results == nil || tup.Len() != ctx.results.Len() {
						return refuse("multi-value return arity")
					}
					if _, ok := e.unseqCall(call, ctx, &d, 2); !ok {
						return refuse("multi-value return call")
					}
					break
				}
			}
		}
		if ctx.results == nil || ctx.results.Len() != len(st.Results) {
			return refuse("return arity")
		}
		for i, r := range st.Results {
			if !unseqTypeOK(ctx.results.At(i).Type()) {
				return refuse("result type outside the pilot grammar (" + ctx.results.At(i).Type().String() + ")")
			}
			if _, ok := e.unseqExpr(r, ctx, &d); !ok {
				return refuse("return operand")
			}
		}
	case *ast.ExprStmt:
		call, isCall := ast.Unparen(st.X).(*ast.CallExpr)
		if !isCall {
			return refuse("expression statement that is not a call")
		}
		if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
			if _, isBuiltin := e.info.Uses[id].(*types.Builtin); isBuiltin {
				switch id.Name {
				case "print", "println":
					d.form = "print-stmt"
					if len(call.Args) == 0 {
						return refuse("print with zero operands")
					}
					for _, a := range call.Args {
						t := e.goTypeOf(a)
						if t == nil || !unseqTypeOK(t) {
							return refuse("print operand type outside the pilot grammar")
						}
						if _, isIface := types.Unalias(t).Underlying().(*types.Interface); isIface {
							return refuse("print of an interface value")
						}
						if _, ok := e.unseqExpr(a, ctx, &d); !ok {
							return refuse("print operand")
						}
					}
					break
				default:
					d.form = "call-stmt"
					return refuse("builtin " + id.Name + " statement")
				}
				break
			}
		}
		if d.form == "other" {
			d.form = "call-stmt"
			if _, ok := e.unseqCall(call, ctx, &d, 2); !ok {
				return refuse("call statement")
			}
		}
	default:
		return refuse("statement form outside the pilot grammar")
	}
	d.admitted = d.reason == "" && d.calls >= 1 && d.nonEvents >= 1
	if d.reason == "" && !d.admitted {
		if d.calls == 0 {
			d.reason = "no call occurrence (legacy path: nothing with an effect to reorder against)"
		} else {
			d.reason = "no non-event occurrence beside the call(s) (legacy path: every edge forced)"
		}
	}
	return d
}

// unseqReadWriteTarget classifies a compound/IncDec target: a local
// identifier (an address-taken local's load is a read occurrence; a
// private local's target plan is order-transparent) or a slice element.
func (e *emitter) unseqReadWriteTarget(lv ast.Expr, ctx *unseqCtx, d *unseqDecision) bool {
	switch l := ast.Unparen(lv).(type) {
	case *ast.Ident:
		loc, ok := e.unseqLocalTarget(l, false, ctx, d)
		if !ok {
			return false
		}
		if _, isIface := types.Unalias(loc.Type()).Underlying().(*types.Interface); isIface {
			if d.reason == "" {
				d.reason = "compound assignment on an interface-typed local"
			}
			return false
		}
		if e.unseqAddrTaken(ctx.body)[e.info.Uses[l]] {
			d.nonEvents++ // the load through the target reads a mutable location
		}
		return true
	case *ast.IndexExpr:
		return e.unseqElemTarget(l, ctx, d)
	}
	if d.reason == "" {
		d.reason = "read-write target outside the pilot grammar"
	}
	return false
}

// unseqCensusRow is one line of `--unseq-census`.
type unseqCensusRow struct {
	fn  string
	pos token.Position
	dec unseqDecision
}

// unseqCensus runs the classifier over EVERY statement list of a
// function body (nested blocks, if/for/switch/select bodies — the
// positions emitStmtList emits) and, recursively, over every func
// literal's body as its own function (with the literal's free captures
// as its captured set). Sub-accumulator sweeps (if/for heads, switch
// tags, range operands) are not statements of a list and are not
// visited: they stay on the legacy path by construction.
func (e *emitter) unseqCensus(name string, body *ast.BlockStmt, results *types.Tuple, captured map[types.Object]bool, out *[]unseqCensusRow) {
	if body == nil {
		return
	}
	ctx := &unseqCtx{body: body, captured: captured, results: results}
	var visitList func(list []ast.Stmt)
	var visitStmt func(s ast.Stmt)
	visitList = func(list []ast.Stmt) {
		for _, s := range list {
			*out = append(*out, unseqCensusRow{fn: name, pos: e.fset.Position(s.Pos()), dec: e.unseqClassify(s, ctx)})
			visitStmt(s)
		}
	}
	visitStmt = func(s ast.Stmt) {
		switch st := s.(type) {
		case *ast.BlockStmt:
			visitList(st.List)
		case *ast.IfStmt:
			visitList(st.Body.List)
			if st.Else != nil {
				visitStmt(st.Else)
			}
		case *ast.ForStmt:
			visitList(st.Body.List)
		case *ast.RangeStmt:
			visitList(st.Body.List)
		case *ast.SwitchStmt:
			for _, c := range st.Body.List {
				if cc, ok := c.(*ast.CaseClause); ok {
					visitList(cc.Body)
				}
			}
		case *ast.TypeSwitchStmt:
			for _, c := range st.Body.List {
				if cc, ok := c.(*ast.CaseClause); ok {
					visitList(cc.Body)
				}
			}
		case *ast.SelectStmt:
			for _, c := range st.Body.List {
				if cc, ok := c.(*ast.CommClause); ok {
					visitList(cc.Body)
				}
			}
		case *ast.LabeledStmt:
			visitStmt(st.Stmt)
		}
	}
	visitList(body.List)
	// Func literals: their own units.
	ast.Inspect(body, func(n ast.Node) bool {
		lit, ok := n.(*ast.FuncLit)
		if !ok {
			return true
		}
		inner := map[types.Object]bool{}
		for k := range captured {
			inner[k] = true
		}
		for _, v := range e.freeCaptures(lit) {
			inner[v] = true
		}
		sig, _ := e.goTypeOf(lit).(*types.Signature)
		var res *types.Tuple
		if sig != nil {
			res = sig.Results()
		}
		e.unseqCensus(name+"$lit@"+e.fset.Position(lit.Pos()).String(), lit.Body, res, inner, out)
		return false // the literal's nested literals are visited by the recursive call
	})
}

// printUnseqCensus is the `--unseq-census` mode (main.go): every function
// and method body of the main unit's files, in file order, through
// `unseqCensus`; one TSV row per sweep on stdout. Header first; the
// `dir` column lets a corpus-wide aggregation keep packages apart.
func (e *emitter) printUnseqCensus(files []*ast.File, dir string) error {
	rows := []unseqCensusRow{}
	units := e.units
	if units == nil {
		units = []*sourcePkg{{path: e.pkg.Path(), files: files, info: e.info, pkg: e.pkg}}
	}
	mainInfo, mainPkg, mainUnit := e.info, e.pkg, e.curUnit
	defer func() { e.info, e.pkg, e.curUnit = mainInfo, mainPkg, mainUnit }()
	out := "dir\tunit\tfile:line\tfunction\tform\tadmitted\tevents\tcalls\tnonEvents\treason\n"
	for _, u := range units {
		e.setUnit(u)
		rows = rows[:0]
		e.unseqCensusUnit(u.files, &rows)
		for _, r := range rows {
			adm := "legacy"
			if r.dec.admitted {
				adm = "unseq"
			}
			out += dir + "\t" + u.path + "\t" + r.pos.Filename + ":" + itoa(r.pos.Line) + "\t" + r.fn + "\t" + r.dec.form + "\t" + adm + "\t" +
				itoa(r.dec.events) + "\t" + itoa(r.dec.calls) + "\t" + itoa(r.dec.nonEvents) + "\t" + r.dec.reason + "\n"
		}
	}
	_, err := os.Stdout.WriteString(out)
	return err
}

// unseqCensusUnit: every function and method body of one unit's files.
func (e *emitter) unseqCensusUnit(files []*ast.File, rows *[]unseqCensusRow) {
	for _, f := range files {
		for _, decl := range f.Decls {
			fd, ok := decl.(*ast.FuncDecl)
			if !ok || fd.Body == nil {
				continue
			}
			obj := e.info.Defs[fd.Name]
			if obj == nil {
				continue
			}
			sig, _ := obj.Type().(*types.Signature)
			var results *types.Tuple
			if sig != nil {
				results = sig.Results()
			}
			name := fd.Name.Name
			if fd.Recv != nil && sig != nil && sig.Recv() != nil {
				name = types.TypeString(sig.Recv().Type(), func(*types.Package) string { return "" }) + "." + name
			}
			e.unseqCensus(name, fd.Body, results, nil, rows)
		}
	}
}
