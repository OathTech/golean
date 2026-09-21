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
// pointers, fields, maps, arrays, strings indexing, methods,
// receives, sends, conversions, allocations, `recover`, multi-target
// assignment, blank targets, sub-accumulator sweeps (if/for/switch
// heads) — sends the WHOLE sweep to the legacy path, by name.
//
// STAGE E, family E1 (lane core/unseq-stage-e-0921, 2026-09-21; v2.1 §7 row
// E; the width-of-P ruling «ALL mutable reads, STAGED» widened one kind):
// a PACKAGE-LEVEL VARIABLE — unqualified `g` or source-package qualified
// `pkg.V` — of an admitted type is a mutable location: its read is a READ
// occurrence (`deref(globaladdr)`, the frontend's spelling of a global
// read) and counts toward `nonEvents`; as an assignment / compound /
// IncDec TARGET its identity has no operands (a plan that checks
// nothing), so the store rides `then` exactly like an address-taken
// local's and the compound form's load is the same READ occurrence. This
// is the family that closes BUG-113: the `&&`/`||` sweeps whose only
// out-of-grammar operand was a package variable now lower as graphs,
// where the guard protocol anchors a later call's E1 edge at the
// COMPLETION. Whether the global's cell is SEEDED (`globalAddr`) is the
// LOWERING's check, not the classifier's — the census runs before the
// globals table exists (`emitProgram` builds it), and the two must not
// drift; an unseeded or FR-24-poisoned global refuses by name at the
// lowering exactly as the legacy path does (the same per-declaration
// quarantine).
//
// STAGE E, family E2 (2026-09-21): POINTERS, FIELDS, MAPS. A read through a
// pointer (`*p`), a field selection (`p.f` through a pointer — nil check +
// load — or `s.f` on a struct variable), and a map element read (`m[k]`) are
// READ occurrences of mutable locations (`deref`, `field-get`, `map-get`
// heads over atoms); as TARGETS (`*p = e`, `p.f = e`, `s.f = e`, `m[k] = e`
// and the compound / IncDec forms) they are FROZEN target plans — the pointer
// VALUE, the struct's address, the map VALUE and the key VALUE — shared by the
// load and the phase-2 store (v2.1 §3.4); a plan whose operands are all atoms
// (a private pointer / struct / map local, a constant key) checks nothing and
// reads nothing, so it does not by itself admit a sweep — the compound forms'
// LOAD is the mutable read that does. TYPES widen with the operands: pointers
// to admitted types, named struct types whose fields are admitted (cycle-
// guarded), maps with an int/bool/string key (never an interface-containing
// key: the boxed key would sit inside the graph) and an admitted value.
// Promoted (embedded-hop) selectors, interface-typed pointees / fields /
// map values as targets, and nested value bases of a field target
// (`a[i].f = e`) stay legacy by name.
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
	return unseqTypeOKSeen(t, map[*types.Named]bool{})
}

// unseqTypeOKSeen is unseqTypeOK with the named types under examination (a
// struct whose field points back at it is admitted once, never re-entered).
func unseqTypeOKSeen(t types.Type, seen map[*types.Named]bool) bool {
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
		return unseqTypeOKSeen(u.Elem(), seen)
	case *types.Interface:
		return u.Empty()
	case *types.Pointer:
		// Stage E E2: a pointer to an admitted type (its VALUE is an atom; the
		// deref is the occurrence).
		return unseqTypeOKSeen(u.Elem(), seen)
	case *types.Map:
		// Stage E E2: an int/bool/string key (a hash-safe, unboxed key) and an
		// admitted value type.
		kb, isBasic := types.Unalias(u.Key()).Underlying().(*types.Basic)
		if !isBasic || kb.Info()&(types.IsInteger|types.IsBoolean|types.IsString) == 0 {
			return false
		}
		if _, keyNamed := types.Unalias(u.Key()).(*types.Named); keyNamed {
			return false // a defined key type is outside (named non-struct types are E5's)
		}
		return unseqTypeOKSeen(u.Elem(), seen)
	case *types.Named:
		// Stage E E2: a NAMED STRUCT type (non-generic) whose every field is an
		// admitted type — the base of a field selection or target.
		if u.TypeArgs().Len() > 0 || u.TypeParams().Len() > 0 {
			return false
		}
		st, isStruct := u.Underlying().(*types.Struct)
		if !isStruct {
			return false
		}
		if seen[u] {
			return true
		}
		seen[u] = true
		for i := 0; i < st.NumFields(); i++ {
			if st.Field(i).Embedded() || !unseqTypeOKSeen(st.Field(i).Type(), seen) {
				return false
			}
		}
		return true
	}
	return false
}

// unseqFieldSel classifies a FIELD selection `x.f` (never a method, never a
// qualified name, never a promoted hop): the base type (a pointer to a named
// struct, or a named struct), the struct's wire name, and whether the base is
// a pointer. `ok` false names the reason in d.
func (e *emitter) unseqFieldSel(v *ast.SelectorExpr, d *unseqDecision) (isPtr bool, structName string, ok bool) {
	refuse := func(why string) (bool, string, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return false, "", false
	}
	seln, isSel := e.info.Selections[v]
	if !isSel || seln.Kind() != types.FieldVal {
		return refuse("selector (method / method value / qualified name)")
	}
	if len(seln.Index()) != 1 {
		return refuse("promoted field selector (embedded hops)")
	}
	bt := e.goTypeOf(v.X)
	if bt == nil {
		return refuse("field selector on an untyped base")
	}
	structT := bt
	if ptr, ok := types.Unalias(bt).Underlying().(*types.Pointer); ok {
		isPtr = true
		structT = ptr.Elem()
	}
	name, named := e.namedTypeName(structT)
	if !named {
		return refuse("field selector on an anonymous struct type")
	}
	if !unseqTypeOK(structT) {
		return refuse("field selector on a struct type outside the grammar (" + structT.String() + ")")
	}
	if !unseqTypeOK(e.goTypeOf(v)) {
		return refuse("field type outside the grammar (" + e.goTypeOf(v).String() + ")")
	}
	return isPtr, name, true
}

// unseqMapBase classifies a map-typed base: the map type when admitted.
func (e *emitter) unseqMapBase(x ast.Expr, d *unseqDecision) (*types.Map, bool) {
	bt := e.goTypeOf(x)
	if bt == nil {
		if d.reason == "" {
			d.reason = "map element on an untyped base"
		}
		return nil, false
	}
	mt, isMap := types.Unalias(bt).Underlying().(*types.Map)
	if !isMap {
		return nil, false
	}
	if !unseqTypeOK(bt) {
		if d.reason == "" {
			d.reason = "map type outside the grammar (" + bt.String() + ")"
		}
		return nil, false
	}
	return mt, true
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
			if pv, isPkg := e.isPackageVar(obj); isPkg {
				// Stage E E1: a package-level variable's read is a READ
				// occurrence of a mutable location (`deref(globaladdr)`).
				if !unseqTypeOK(pv.Type()) {
					return refuse("package-level variable of a type outside the grammar (" + pv.Type().String() + ")")
				}
				d.nonEvents++
				return unseqValue, true
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
		if _, isMap := types.Unalias(bt).Underlying().(*types.Map); isMap {
			// Stage E E2: a map element READ — base and key are producers, the
			// lookup is ONE occurrence (a mutable read; the key is hash-safe by
			// the type grammar, so it cannot panic — still an occurrence: it
			// reads the map at that instant).
			if _, ok := e.unseqMapBase(v.X, d); !ok {
				return unseqConst, false
			}
			if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
				return unseqConst, false
			}
			if _, ok := e.unseqExpr(v.Index, ctx, d); !ok {
				return unseqConst, false
			}
			d.nonEvents++
			return unseqValue, true
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
		// Stage E E2: `*p` — the pointer VALUE is the producer, the dereference
		// ONE occurrence (a nil check + a mutable read).
		pt := e.goTypeOf(v.X)
		if pt == nil || !unseqTypeOK(pt) {
			return refuse("pointer indirection on a pointer type outside the grammar")
		}
		if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
			return unseqConst, false
		}
		d.nonEvents++
		return unseqValue, true
	case *ast.SelectorExpr:
		if pv, ok := e.unseqQualifiedPackageVar(v); ok {
			// Stage E E1: `pkg.V` (a source-package qualified package-level
			// variable, W1.1) is name resolution, not selection — the same
			// READ occurrence as the unqualified spelling.
			if !unseqTypeOK(pv.Type()) {
				return refuse("qualified package-level variable of a type outside the grammar (" + pv.Type().String() + ")")
			}
			d.nonEvents++
			return unseqValue, true
		}
		// Stage E E2: a FIELD read. Through a pointer: the pointer value is the
		// producer, the selection ONE occurrence (nil check + mutable read). On a
		// struct VALUE: the base's own classification decides (an address-taken
		// struct local's read is the occurrence — the lowering fuses it with the
		// selection into one `field-get` read; a private struct local's field is
		// a stable read, order-transparent; a nested value base produces a slot).
		isPtr, _, ok := e.unseqFieldSel(v, d)
		if !ok {
			return unseqConst, false
		}
		if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
			return unseqConst, false
		}
		if isPtr {
			d.nonEvents++
		}
		return unseqValue, true
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

// unseqQualifiedPackageVar recognizes `pkg.V` — a source-package qualified
// PACKAGE-LEVEL VARIABLE (W1.1's name resolution, never a field selection).
func (e *emitter) unseqQualifiedPackageVar(sel *ast.SelectorExpr) (*types.Var, bool) {
	if _, ok := e.qualifiedPkgRef(sel); !ok {
		return nil, false
	}
	return e.isPackageVar(e.info.Uses[sel.Sel])
}

// unseqVarTarget classifies an assignment target that is a plain variable
// identifier: a LOCAL variable (not blank, not a captured variable inside a
// lifted body) or — Stage E E1 — a PACKAGE-LEVEL variable, of an admitted
// type. `define` selects Defs (a fresh `:=` declaration) over Uses. The
// second result is true for a package-level variable (its target identity
// has no operands; the store rides `then`).
func (e *emitter) unseqVarTarget(id *ast.Ident, define bool, ctx *unseqCtx, d *unseqDecision) (*types.Var, bool, bool) {
	refuse := func(why string) (*types.Var, bool, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return nil, false, false
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
		if pv, isPkg := e.isPackageVar(obj); isPkg && !define {
			if !unseqTypeOK(pv.Type()) {
				return refuse("package-level target of a type outside the grammar (" + pv.Type().String() + ")")
			}
			return pv, true, true
		}
		return refuse("non-local target")
	}
	if ctx.captured[obj] {
		return refuse("captured target written through its pointer parameter (lifted body)")
	}
	if !unseqTypeOK(loc.Type()) {
		return refuse("target type outside the pilot grammar (" + loc.Type().String() + ")")
	}
	return loc, false, true
}

// unseqQualifiedTarget classifies a `pkg.V` assignment target (Stage E E1):
// a source-package qualified package-level variable of an admitted type.
func (e *emitter) unseqQualifiedTarget(sel *ast.SelectorExpr, d *unseqDecision) (*types.Var, bool) {
	pv, ok := e.unseqQualifiedPackageVar(sel)
	if !ok {
		if d.reason == "" {
			d.reason = "assignment target outside the pilot grammar"
		}
		return nil, false
	}
	if !unseqTypeOK(pv.Type()) {
		if d.reason == "" {
			d.reason = "qualified package-level target of a type outside the grammar (" + pv.Type().String() + ")"
		}
		return nil, false
	}
	return pv, true
}

// unseqCtxNow is the classifier's context for the function whose statements
// the emitter is emitting (nil outside any function body): its body, the
// variables reached through capture pointers in a lifted body, its results.
func (e *emitter) unseqCtxNow() *unseqCtx {
	if e.unseqBody == nil {
		return nil
	}
	captured := map[types.Object]bool{}
	for obj := range e.captureParam {
		captured[obj] = true
	}
	return &unseqCtx{body: e.unseqBody, captured: captured, results: e.curResults}
}

// unseqElemTarget classifies a slice-element target `a[i]`: base and index
// inside the grammar; the target PLAN is a non-event occurrence (frozen
// header + index, one identity for the load and the store — v2.1 §3.4). An
// interface-typed element is outside the pilot (its store would box the
// value inside the graph; boxing is an argument/completion wrap here).
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
	if _, isIface := types.Unalias(sl.Elem()).Underlying().(*types.Interface); isIface {
		return refuse("interface-typed element target (boxing inside a graph is outside the pilot)")
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

// unseqDerefTarget classifies a dereference target `*p` (Stage E E2): the
// pointer operand inside the grammar, an admitted non-interface pointee. The
// plan FREEZES the pointer VALUE and checks nothing (nil at the store, phase 2);
// it is an occurrence only through its operand (a read of an address-taken or
// package-level pointer counts there), so it does not by itself admit a sweep.
func (e *emitter) unseqDerefTarget(st *ast.StarExpr, ctx *unseqCtx, d *unseqDecision) bool {
	refuse := func(why string) bool {
		if d.reason == "" {
			d.reason = why
		}
		return false
	}
	pt := e.goTypeOf(st.X)
	if pt == nil || !unseqTypeOK(pt) {
		return refuse("dereference target on a pointer type outside the grammar")
	}
	ptr, isPtr := types.Unalias(pt).Underlying().(*types.Pointer)
	if !isPtr {
		return refuse("dereference target on a non-pointer")
	}
	if _, isIface := types.Unalias(ptr.Elem()).Underlying().(*types.Interface); isIface {
		return refuse("interface-typed dereference target (boxing inside a graph is outside the grammar)")
	}
	if _, ok := e.unseqExpr(st.X, ctx, d); !ok {
		return false
	}
	return true
}

// unseqFieldTarget classifies a field target `p.f` / `s.f` (Stage E E2): a
// non-promoted field of a named struct, reached through a pointer operand
// inside the grammar or on a struct VARIABLE (a local or a package-level
// variable — its address is the frozen anchor); a nested value base
// (`a[i].f = e`) is outside. The plan checks nothing (nil at the store).
func (e *emitter) unseqFieldTarget(sel *ast.SelectorExpr, ctx *unseqCtx, d *unseqDecision) bool {
	refuse := func(why string) bool {
		if d.reason == "" {
			d.reason = why
		}
		return false
	}
	isPtr, _, ok := e.unseqFieldSel(sel, d)
	if !ok {
		return false
	}
	if _, isIface := types.Unalias(e.goTypeOf(sel)).Underlying().(*types.Interface); isIface {
		return refuse("interface-typed field target (boxing inside a graph is outside the grammar)")
	}
	if isPtr {
		if _, ok := e.unseqExpr(sel.X, ctx, d); !ok {
			return false
		}
		return true
	}
	id, isIdent := ast.Unparen(sel.X).(*ast.Ident)
	if !isIdent {
		return refuse("field target on a non-variable struct base")
	}
	obj := e.info.Uses[id]
	if _, isLocal := e.unseqLocalVar(obj); isLocal {
		if ctx.captured[obj] {
			return refuse("field target on a captured struct variable (lifted body)")
		}
		return true // the struct variable's address is the frozen anchor (no read)
	}
	if _, isPkg := e.isPackageVar(obj); isPkg {
		return true
	}
	return refuse("field target on a non-variable struct base")
}

// unseqMapTarget classifies a map-element target `m[k]` (Stage E E2): base and
// key inside the grammar (the map type admitted — an int/bool/string key, an
// admitted non-interface value). The plan FREEZES the map VALUE and the key
// VALUE — one identity for the load and the store (v2.1 §3.4); its checks
// (nil map) are the store's, phase 2.
func (e *emitter) unseqMapTarget(ix *ast.IndexExpr, ctx *unseqCtx, d *unseqDecision) bool {
	refuse := func(why string) bool {
		if d.reason == "" {
			d.reason = why
		}
		return false
	}
	mt, ok := e.unseqMapBase(ix.X, d)
	if !ok {
		return refuse("map element target on a base outside the grammar")
	}
	if _, isIface := types.Unalias(mt.Elem()).Underlying().(*types.Interface); isIface {
		return refuse("interface-typed map value target (boxing inside a graph is outside the grammar)")
	}
	if _, ok := e.unseqExpr(ix.X, ctx, d); !ok {
		return false
	}
	if _, ok := e.unseqExpr(ix.Index, ctx, d); !ok {
		return false
	}
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
				if _, _, ok := e.unseqVarTarget(l, define, ctx, &d); !ok {
					return refuse("target")
				}
			case *ast.SelectorExpr:
				if define {
					return refuse("define with a selector target")
				}
				if _, isQual := e.unseqQualifiedPackageVar(l); isQual {
					if _, ok := e.unseqQualifiedTarget(l, &d); !ok {
						return refuse("target")
					}
				} else {
					d.form = "field-assign"
					if !e.unseqFieldTarget(l, ctx, &d) {
						return refuse("target")
					}
				}
			case *ast.IndexExpr:
				if define {
					return refuse("define with an index target")
				}
				if _, isMap := e.unseqMapBase(l.X, &d); isMap {
					d.form = "map-assign"
					if !e.unseqMapTarget(l, ctx, &d) {
						return refuse("target")
					}
				} else {
					d.form = "elem-assign"
					if !e.unseqElemTarget(l, ctx, &d) {
						return refuse("target")
					}
				}
			case *ast.StarExpr:
				if define {
					return refuse("define with a dereference target")
				}
				d.form = "deref-assign"
				if !e.unseqDerefTarget(l, ctx, &d) {
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

// unseqReadWriteTarget classifies a compound/IncDec target: a variable
// identifier (an address-taken local's or a package-level variable's load
// is a READ occurrence of a mutable location — Stage E E1 for the latter; a
// private local's target plan is order-transparent), a `pkg.V` qualified
// package-level variable, or a slice element.
func (e *emitter) unseqReadWriteTarget(lv ast.Expr, ctx *unseqCtx, d *unseqDecision) bool {
	switch l := ast.Unparen(lv).(type) {
	case *ast.Ident:
		loc, isPkg, ok := e.unseqVarTarget(l, false, ctx, d)
		if !ok {
			return false
		}
		if _, isIface := types.Unalias(loc.Type()).Underlying().(*types.Interface); isIface {
			if d.reason == "" {
				d.reason = "compound assignment on an interface-typed variable"
			}
			return false
		}
		if isPkg || e.unseqAddrTaken(ctx.body)[e.info.Uses[l]] {
			d.nonEvents++ // the load through the target reads a mutable location
		}
		return true
	case *ast.SelectorExpr:
		if _, isQual := e.unseqQualifiedPackageVar(l); !isQual {
			// Stage E E2: a field compound target — the plan (frozen base), the
			// LOAD a mutable read.
			if !e.unseqFieldTarget(l, ctx, d) {
				return false
			}
			d.nonEvents++
			return true
		}
		pv, ok := e.unseqQualifiedTarget(l, d)
		if !ok {
			return false
		}
		if _, isIface := types.Unalias(pv.Type()).Underlying().(*types.Interface); isIface {
			if d.reason == "" {
				d.reason = "compound assignment on an interface-typed variable"
			}
			return false
		}
		d.nonEvents++ // the load of a package-level variable is a mutable read
		return true
	case *ast.IndexExpr:
		if _, isMap := e.unseqMapBase(l.X, d); isMap {
			// Stage E E2: a map compound target — the plan (frozen map VALUE and
			// key VALUE, one identity for the load and the store), the LOAD a
			// mutable read.
			if !e.unseqMapTarget(l, ctx, d) {
				return false
			}
			d.nonEvents++
			return true
		}
		return e.unseqElemTarget(l, ctx, d)
	case *ast.StarExpr:
		// Stage E E2: `*p op= e` — the plan freezes the pointer VALUE; the LOAD
		// is a mutable read (nil-checked).
		if !e.unseqDerefTarget(l, ctx, d) {
			return false
		}
		d.nonEvents++
		return true
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
