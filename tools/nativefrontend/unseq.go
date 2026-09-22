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
// STAGE E, family E3 (2026-09-21): RECEIVES and METHOD CALLS. A receive
// `<-ch` in operand position is an EVENT occurrence (spec#Order_of_evaluation
// orders receives lexically among the calls — E1; the communication happens
// once; the value lands in a predeclared binder) — it counts toward the
// trigger like a call (an effect); the channel operand is an atom or a
// produced value (channel types of admitted element types enter the type
// grammar). A METHOD CALL on a CONCRETE receiver (a named struct, or a pointer
// to one; never an interface — dynamic dispatch has no callee VALUE) is an
// invocation whose callee is the method's function value and whose first
// argument is the receiver sub-evaluation (E14's sub-axis): a pointer
// receiver on a pointer operand passes the pointer atom; on an addressable
// variable, its address (a frozen `ref`, no read); on `*p`, the nil-asserting
// `addr-of-deref` — an occurrence that may fail; a value receiver copies the
// operand (an address-taken variable's read is the occurrence) or, through a
// pointer, dereferences it (an occurrence). Promoted methods, method values
// and expressions, interface methods, generic methods stay legacy by name.
// The comma-ok receive is E5's (a two-binder occurrence).
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
	events    int    // every invocation-kind occurrence: calls, receives AND non-constant len/cap (E1-ordered)
	calls     int    // the EFFECTFUL events among them — calls and receives; the trigger counts these
	nonEvents int

	// THE OBSERVABILITY RECORD (Stage E E3, 2026-09-21). The E1 PARTICIPANTS of the
	// sweep — calls, receives, non-constant len/cap, `&&`/`||` guards — are numbered
	// in COMPLETION order (`seq`: the order the lowering's E1 anchor chain
	// realizes); an open participant holds an OPEN id on `open` until it completes,
	// `closeIdx` maps the id to its completion index, `effect` marks the effectful
	// ones (calls, receives). Every non-event occurrence records the innermost
	// participant it lies inside (`anc`: an open id, or -1) and `lo`, the first
	// participant index NOT forced before it — 0 when it consumes no participant
	// (an earlier participant is then a sibling, unordered against it), else one
	// past the last participant completed inside its own operand window (those it
	// consumes, and every participant completing before one of them, precede it).
	// The occurrence is OBSERVABLE against an effectful event X iff lo <= X < the
	// completion index of `anc` (an occurrence inside a participant's operand
	// subtree precedes that participant and hence every later one). A guard's
	// window holds its own region, so it is observable iff an effectful event
	// completes AFTER it — the later event is anchored at the guard's COMPLETION
	// (BUG-113's fix; the legacy hoister realizes the wrong order there). A sweep is
	// admitted iff some occurrence is observable: every other in-grammar sweep with
	// a call has every edge forced, and the legacy path realizes that unique order
	// exactly (the pilot's trigger rationale, made precise).
	seq      int
	open     []int
	nextOpen int
	closeIdx map[int]int
	effect   map[int]bool
	occs     []unseqOccRec
}

// unseqOccRec is one non-event occurrence's observability record.
type unseqOccRec struct {
	anc int // the innermost enclosing participant's OPEN id, -1 at the top level
	lo  int // the first participant index not forced before the occurrence
}

// openP opens an E1 participant (a call, a receive, a len/cap, a guard) around
// the classification of its operand subtree; closeP completes it.
func (d *unseqDecision) openP() int {
	id := d.nextOpen
	d.nextOpen++
	d.open = append(d.open, id)
	return id
}

func (d *unseqDecision) closeP(id int, effect bool) {
	if n := len(d.open); n > 0 && d.open[n-1] == id {
		d.open = d.open[:n-1]
	}
	if d.closeIdx == nil {
		d.closeIdx = map[int]int{}
		d.effect = map[int]bool{}
	}
	d.closeIdx[id] = d.seq
	d.effect[d.seq] = effect
	d.seq++
}

// occ records one non-event occurrence (the census column AND the observability
// record); `start` is the participant count when the occurrence's OWN operand
// classification began.
func (d *unseqDecision) occ(start int) {
	d.nonEvents++
	anc := -1
	if n := len(d.open); n > 0 {
		anc = d.open[n-1]
	}
	lo := 0
	if d.seq > start {
		lo = d.seq
	}
	d.occs = append(d.occs, unseqOccRec{anc: anc, lo: lo})
}

// observable decides the trigger from the record (the struct's comment).
func (d *unseqDecision) observable() bool {
	for _, o := range d.occs {
		hi := d.seq
		if o.anc >= 0 {
			if c, done := d.closeIdx[o.anc]; done {
				hi = c
			}
		}
		for x := o.lo; x < hi; x++ {
			if d.effect[x] {
				return true
			}
		}
	}
	return false
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
	case *types.Chan:
		// Stage E E3: a channel of an admitted element type (its VALUE is an
		// atom; the receive is the event).
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
					// Stage E E3 (2026-09-21): the implicit `&x` exists only for a
					// POINTER-receiver method on a NON-pointer operand (spec#Calls:
					// `x.m()` is `(&x).m()`); a pointer operand passes its VALUE and a
					// value receiver copies — no address of the variable is taken.
					// Stage C marked every method-call operand conservatively.
					if fn, isFn := s.Obj().(*types.Func); isFn {
						if sig, isSig := fn.Type().(*types.Signature); isSig && sig.Recv() != nil {
							_, recvIsPtr := types.Unalias(sig.Recv().Type()).Underlying().(*types.Pointer)
							_, opIsPtr := types.Unalias(e.goTypeOf(sel.X)).Underlying().(*types.Pointer)
							if recvIsPtr && !opIsPtr {
								mark(unseqRootIdent(sel.X))
							}
						}
					}
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
	unseqAddr                       // Stage E5 E5d: the ADDRESS of a variable (`&x`): no read, no failure — an argument / payload / stored value, never a head's operand
)

// unseqValueOrAddr classifies an operand in a VALUE position whose consumer takes
// an already-evaluated value (Stage E5 E5d, 2026-09-22): `&x` of a local or
// package-level variable is an ADDRESS FORMATION — spec#Address_operators: it
// reads nothing and cannot fail (the operand is a variable, not `*p`) — lowered as
// `ref x` / `globaladdr` (the frontend's own address spelling); every other
// operand is `unseqExpr`'s. Positions that COMPUTE on their operand (an index, a
// dereference, a comparison, a conversion, a head) call `unseqExpr` directly,
// where `&x` refuses by name — the decoder admits `ref` only as an invocation
// argument or an allocation payload (never as a head), so the classifier's allowed
// list mirrors the decoder's; a PLANNED target's copied value is refused by name at
// its site (the store would copy a `ref` head into a cell).
func (e *emitter) unseqValueOrAddr(x ast.Expr, ctx *unseqCtx, d *unseqDecision) (unseqExprKind, bool) {
	if id, isAddr := unseqAddrOfVar(x); isAddr {
		pt := e.goTypeOf(x)
		if pt == nil || !unseqTypeOK(pt) {
			if d.reason == "" {
				d.reason = "address of a variable of a type outside the grammar (" + typeStringOrUntyped(pt) + ")"
			}
			return unseqConst, false
		}
		obj := e.info.Uses[id]
		if _, isLocal := e.unseqLocalVar(obj); isLocal {
			return unseqAddr, true
		}
		if _, isPkg := e.isPackageVar(obj); isPkg {
			return unseqAddr, true
		}
		if d.reason == "" {
			d.reason = "address of a non-variable identifier"
		}
		return unseqConst, false
	}
	return e.unseqExpr(x, ctx, d)
}

// unseqAddrOfVar reports `&ident` (parenthesised or not) — the address of a named variable,
// as opposed to `&T{…}` (an allocation, E4) or `&a[i]` / `&s.f` (outside the grammar).
func unseqAddrOfVar(x ast.Expr) (*ast.Ident, bool) {
	u, isUnary := ast.Unparen(x).(*ast.UnaryExpr)
	if !isUnary || u.Op != token.AND {
		return nil, false
	}
	id, isIdent := ast.Unparen(u.X).(*ast.Ident)
	return id, isIdent
}

// unseqExpr classifies an operand expression: whether it lies inside the
// pilot expression grammar (reason names the first construct outside it),
// what it lowers to, and how many event / non-event occurrences it
// carries. `valuePos` is true where a value is required (false only for
// the callee-position and statement-position calls handled by callers).
func (e *emitter) unseqExpr(x ast.Expr, ctx *unseqCtx, d *unseqDecision) (unseqExprKind, bool) {
	start := d.seq // the occurrence window's start (unseqDecision.occ)
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
				d.occ(start)
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
			d.occ(start) // a mutable read: the pilot's P(ii) read
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
			d.occ(start)
			return unseqValue, true
		}
		if isStringType(types.Unalias(bt).Underlying()) {
			// Stage E5 E5e (2026-09-22): a STRING index `s[i]` — a byte read of an immutable value,
			// bounds-checked: a FAILING PURE OP on the string VALUE and index VALUE (the machine's
			// `indexGet` on a string; spec#Index_expressions). The string's own read is the base's
			// classification (a captured / package-level string is a READ occurrence).
			if !unseqTypeOK(bt) {
				return refuse("index of a string type outside the grammar (" + bt.String() + ")")
			}
			if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
				return unseqConst, false
			}
			if _, ok := e.unseqExpr(v.Index, ctx, d); !ok {
				return unseqConst, false
			}
			d.occ(start) // the checked byte read
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
		d.occ(start) // the ONE checked access (N1 SPLIT: base/index are producers)
		return unseqValue, true
	case *ast.SliceExpr:
		bt := e.goTypeOf(v.X)
		if bt == nil {
			return refuse("slice of an untyped base")
		}
		if _, isSlice := types.Unalias(bt).Underlying().(*types.Slice); !isSlice {
			// Stage E5 E5e: a STRING slice `s[lo:hi]` — a substring of an immutable value,
			// bounds-checked (spec#Slice_expressions): a FAILING PURE OP on the string VALUE.
			if !isStringType(types.Unalias(bt).Underlying()) {
				return refuse("slice expression on a non-slice base (" + bt.String() + ")")
			}
			if v.Slice3 {
				return refuse("full slice expression on a string (Go forbids it)")
			}
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
		d.occ(start) // a failing pure op (slice bounds)
		return unseqValue, true
	case *ast.CallExpr:
		if tv, ok := e.info.Types[v.Fun]; ok && tv.IsType() {
			// Stage E E4: a CONVERSION T(x) — a pure op over the operand's value.
			return e.unseqConversion(v, ctx, d)
		}
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
			gid := d.openP() // the guard is an E1 participant: its test and region precede its completion
			if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
				return unseqConst, false
			}
			if _, ok := e.unseqExpr(v.Y, ctx, d); !ok {
				return unseqConst, false
			}
			d.closeP(gid, false)
			d.occ(start) // the guard entry + completion: its window holds its region, so it is observable iff an effectful event FOLLOWS it
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
			d.occ(start) // division/remainder by a non-constant, shift by a non-constant signed count
		}
		return unseqValue, true
	case *ast.UnaryExpr:
		if v.Op == token.ARROW {
			// Stage E E3: a RECEIVE — an E1-ordered EVENT occurrence with an
			// effect (the trigger counts it like a call); one result.
			if _, isTup := e.goTypeOf(v).(*types.Tuple); isTup {
				return refuse("comma-ok receive in expression position")
			}
			ct := e.goTypeOf(v.X)
			if ct == nil || !unseqTypeOK(ct) {
				return refuse("receive on a channel type outside the grammar")
			}
			ch, isChan := types.Unalias(ct).Underlying().(*types.Chan)
			if !isChan || ch.Dir() == types.SendOnly {
				return refuse("receive on a non-receivable channel")
			}
			rid := d.openP()
			if _, ok := e.unseqExpr(v.X, ctx, d); !ok {
				return unseqConst, false
			}
			d.closeP(rid, true)
			d.events++
			d.calls++
			return unseqValue, true
		}
		if v.Op == token.AND {
			// Stage E E4: `&T{…}` — a struct literal's payloads, then an `alloc new`
			// body (no E1 edge, v2.1 R3). The address of a VARIABLE stays outside (E5).
			if cl, isLit := ast.Unparen(v.X).(*ast.CompositeLit); isLit {
				return e.unseqAddrLit(cl, ctx, d)
			}
			// Stage E5 E5d: `&x` is admitted only in VALUE positions (`unseqValueOrAddr`);
			// here a head would compute on the address.
			return refuse("unary operator & (address of a variable) in a computing position — admitted only as an argument, a payload or a stored value (E5d)")
		}
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
		d.occ(start) // a failing pure op (spec#Type_assertions)
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
		d.occ(start)
		return unseqValue, true
	case *ast.SelectorExpr:
		if pv, ok := e.unseqQualifiedPackageVar(v); ok {
			// Stage E E1: `pkg.V` (a source-package qualified package-level
			// variable, W1.1) is name resolution, not selection — the same
			// READ occurrence as the unqualified spelling.
			if !unseqTypeOK(pv.Type()) {
				return refuse("qualified package-level variable of a type outside the grammar (" + pv.Type().String() + ")")
			}
			d.occ(start)
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
			d.occ(start)
		}
		return unseqValue, true
	case *ast.CompositeLit:
		// Stage E E4: a VALUE composite literal — a struct literal (a pure
		// `struct-lit` head) or a slice literal (an `alloc` body).
		return e.unseqCompositeLit(v, ctx, d)
	}
	return refuse("expression outside the pilot grammar")
}

// unseqConversion classifies a conversion T(x) (Stage E E4): a PURE OP over
// the operand's value — integer <-> integer, bool <-> bool (a static
// retyping), string <-> string, string <-> []byte / []rune, integer -> string
// (emitCallNode's operator table) — admitted when both types are in the
// grammar; it cannot fail (slice-to-array conversions are outside the type
// grammar) and is never an occurrence of its own EXCEPT for the two forms
// that read MUTABLE memory: `string([]byte)` / `string([]rune)` copy the
// slice's BACKING ARRAY at the conversion — a mutable read, spec-unordered
// against a sibling call that writes an alias of the slice — so those two are
// occurrences (the Stage E audit's F4, 2026-09-21: the first E4 cut treated
// them as pure over the slice VALUE, which classified `string(b) + m()` — b
// private but aliased, m writing the alias — as all-forced and sent it to the
// legacy path, a (b) pin of gc's order presented as forced; gc's order.go
// call class holds OSTR2BYTES/OSTR2RUNES, not OBYTES2STR/ORUNES2STR). A
// conversion to an interface type is a box (E5's), refused by name.
func (e *emitter) unseqConversion(c *ast.CallExpr, ctx *unseqCtx, d *unseqDecision) (unseqExprKind, bool) {
	start := d.seq // the occurrence window's start (unseqDecision.occ)
	refuse := func(why string) (unseqExprKind, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return unseqConst, false
	}
	if len(c.Args) != 1 {
		return refuse("conversion arity")
	}
	tt := e.goTypeOf(c)
	ot := e.goTypeOf(c.Args[0])
	if tt == nil || ot == nil {
		return refuse("conversion of an untyped operand")
	}
	if _, isIface := types.Unalias(tt).Underlying().(*types.Interface); isIface {
		return refuse("conversion to an interface type (a box — E5)")
	}
	if !unseqTypeOK(tt) {
		return refuse("conversion to a type outside the grammar (" + tt.String() + ")")
	}
	if !unseqTypeOK(ot) {
		return refuse("conversion operand type outside the grammar (" + ot.String() + ")")
	}
	tu, ou := types.Unalias(tt).Underlying(), types.Unalias(ot).Underlying()
	tb, tIsBasic := tu.(*types.Basic)
	ob, oIsBasic := ou.(*types.Basic)
	admitted := false
	switch {
	case tIsBasic && oIsBasic && tb.Info()&types.IsInteger != 0 && ob.Info()&types.IsInteger != 0,
		tIsBasic && oIsBasic && tb.Info()&types.IsBoolean != 0 && ob.Info()&types.IsBoolean != 0,
		tIsBasic && oIsBasic && tb.Info()&types.IsString != 0 && ob.Info()&types.IsString != 0,
		tIsBasic && oIsBasic && tb.Info()&types.IsString != 0 && ob.Info()&types.IsInteger != 0,
		isByteSlice(tu) && isStringType(ou), isStringType(tu) && isByteSlice(ou),
		isRuneSlice(tu) && isStringType(ou), isStringType(tu) && isRuneSlice(ou):
		admitted = true
	}
	if !admitted {
		return refuse("conversion outside the admitted table (" + ot.String() + " -> " + tt.String() + ")")
	}
	if _, ok := e.unseqExpr(c.Args[0], ctx, d); !ok {
		return unseqConst, false
	}
	if isStringType(tu) && (isByteSlice(ou) || isRuneSlice(ou)) {
		d.occ(start) // the backing array's read (audit F4): a mutable read of its own
	}
	return unseqValue, true
}

// unseqMakeNew classifies `make(T, …)` / `new(T)` / `new(x)` (Stage E E4): a
// FUNCTION CALL (spec#Built-in_functions «called like any other function») —
// an E1 participant like len/cap, WITHOUT effect (it does not admit a sweep by
// itself; its size operands' reads — and, for Go 1.26's `new(x)`, the
// argument's reads and calls — are the occurrences and events inside its
// window); the allocation is an `allocate` body. `pid` is the participant the
// caller opened.
func (e *emitter) unseqMakeNew(c *ast.CallExpr, name string, ctx *unseqCtx, d *unseqDecision, pid int) (int, bool) {
	refuse := func(why string) (int, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return 0, false
	}
	t := e.goTypeOf(c)
	if t == nil {
		return refuse(name + " of an untyped result")
	}
	if !unseqTypeOK(t) {
		return refuse(name + " of a type outside the grammar (" + t.String() + ")")
	}
	switch name {
	case "new":
		if len(c.Args) != 1 {
			return refuse("new arity")
		}
		if _, isPtr := types.Unalias(t).Underlying().(*types.Pointer); !isPtr {
			return refuse("new without a pointer result")
		}
		// Go 1.26 `new(x)` (spec#Allocation: «If the argument is an expression x,
		// then new(x) allocates a variable of the type of x initialized to the
		// value of x»): the argument is an OPERAND, classified like a call's
		// argument — its reads are occurrences inside new's window (new is
		// E1-ordered, so they are forced before every later participant), a call
		// inside it an E1-ordered event. The Stage E audit's F1 (2026-09-21): the
		// first E4 cut never inspected the argument — `*new(x) + m()` answered
		// the ZERO value and `*new(m())` never ran m (a wrong answer against gc
		// and main; the census counted `q := new(m())` as events=1 calls=0).
		if tv, ok := e.info.Types[c.Args[0]]; !ok || !tv.IsType() {
			if _, ok := e.unseqValueOrAddr(c.Args[0], ctx, d); !ok {
				return 0, false
			}
		}
	default:
		switch types.Unalias(t).Underlying().(type) {
		case *types.Slice, *types.Map, *types.Chan:
		default:
			return refuse("make of a type outside the grammar (" + t.String() + ")")
		}
		if len(c.Args) < 1 {
			return refuse("make arity")
		}
		for _, a := range c.Args[1:] {
			if _, ok := e.unseqExpr(a, ctx, d); !ok {
				return 0, false
			}
		}
	}
	d.closeP(pid, false)
	d.events++
	return 1, true
}

// unseqMinMax classifies `min(...)` / `max(...)` (Stage E5 E5a, 2026-09-22):
// READING (a) — RATIFIED [USER] 2026-09-22 (relayed) — the built-ins are the
// «function calls» of spec#Order_of_evaluation's ordering sentence, so min/max
// are E1 participants: their operands' reads are occurrences inside their
// window, forced before every later participant; they have no effect and cannot
// fail, so like len/cap/make they do not admit a sweep by themselves. The
// result is a pure `min`/`max` head over the operand atoms (Expr.minOf/maxOf).
func (e *emitter) unseqMinMax(c *ast.CallExpr, name string, ctx *unseqCtx, d *unseqDecision, pid int) (int, bool) {
	refuse := func(why string) (int, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return 0, false
	}
	t := e.goTypeOf(c)
	if t == nil || !unseqTypeOK(t) {
		return refuse(name + " of a type outside the grammar (" + typeStringOrUntyped(t) + ")")
	}
	if len(c.Args) == 0 {
		return refuse(name + " arity")
	}
	for _, a := range c.Args {
		if _, ok := e.unseqExpr(a, ctx, d); !ok {
			return 0, false
		}
	}
	d.closeP(pid, false)
	d.events++
	return 1, true
}

// unseqAppend classifies `append(s, x…)` / `append(s, t...)` (Stage E5 E5a): an
// EFFECTFUL E1 participant (reading (a)) — when the base has capacity the append
// stores the elements IN PLACE in the shared backing array (observable through
// every alias) and always returns a fresh header; the base and element reads are
// occurrences inside its window (forced before every later participant); a
// non-spread element list is packed into a slice literal (an allocate node inside
// the window, as the legacy hoist packs it); a spread string operand is a pure
// bytes-from-string head. Lowered as a `wide` body (`Stmt.appendSlice`).
func (e *emitter) unseqAppend(c *ast.CallExpr, ctx *unseqCtx, d *unseqDecision, pid int) (int, bool) {
	refuse := func(why string) (int, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return 0, false
	}
	t := e.goTypeOf(c)
	if t == nil {
		return refuse("append of an untyped result")
	}
	sl, isSlice := types.Unalias(t).Underlying().(*types.Slice)
	if !isSlice || !unseqTypeOK(t) {
		return refuse("append result type outside the grammar (" + t.String() + ")")
	}
	if len(c.Args) == 0 {
		return refuse("append arity")
	}
	if _, ok := e.unseqExpr(c.Args[0], ctx, d); !ok {
		return 0, false
	}
	if c.Ellipsis != token.NoPos {
		if len(c.Args) != 2 {
			return refuse("append spread arity")
		}
		at := e.goTypeOf(c.Args[1])
		if at == nil {
			return refuse("append spread of an untyped operand")
		}
		au := types.Unalias(at).Underlying()
		_, spreadSlice := au.(*types.Slice)
		if !(spreadSlice && unseqTypeOK(at)) && !(isStringType(au) && isByteSlice(types.Unalias(t).Underlying())) {
			return refuse("append spread operand type outside the grammar (" + at.String() + ")")
		}
		if _, ok := e.unseqExpr(c.Args[1], ctx, d); !ok {
			return 0, false
		}
	} else {
		for _, a := range c.Args[1:] {
			if _, isTup := e.goTypeOf(a).(*types.Tuple); isTup {
				return refuse("multi-value argument")
			}
			if _, ok := e.unseqExpr(a, ctx, d); !ok {
				return 0, false
			}
		}
	}
	_ = sl
	d.closeP(pid, true)
	d.events++
	d.calls++
	return 1, true
}

// unseqCopy classifies `copy(dst, src)` (Stage E5 E5a): an EFFECTFUL E1 participant
// (reading (a)) writing the destination's elements; both operands' reads are
// occurrences inside its window; a string source is a pure bytes-from-string head.
// Lowered as a `wide` body (`Stmt.copySlice`) — in value position (the count) and
// in statement position alike.
func (e *emitter) unseqCopy(c *ast.CallExpr, ctx *unseqCtx, d *unseqDecision, pid int) (int, bool) {
	refuse := func(why string) (int, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return 0, false
	}
	if len(c.Args) != 2 {
		return refuse("copy arity")
	}
	dt := e.goTypeOf(c.Args[0])
	st := e.goTypeOf(c.Args[1])
	if dt == nil || st == nil {
		return refuse("copy of an untyped operand")
	}
	if _, isSlice := types.Unalias(dt).Underlying().(*types.Slice); !isSlice || !unseqTypeOK(dt) {
		return refuse("copy destination type outside the grammar (" + dt.String() + ")")
	}
	su := types.Unalias(st).Underlying()
	_, srcSlice := su.(*types.Slice)
	if !(srcSlice && unseqTypeOK(st)) && !(isStringType(su) && isByteSlice(types.Unalias(dt).Underlying())) {
		return refuse("copy source type outside the grammar (" + st.String() + ")")
	}
	if _, ok := e.unseqExpr(c.Args[0], ctx, d); !ok {
		return 0, false
	}
	if _, ok := e.unseqExpr(c.Args[1], ctx, d); !ok {
		return 0, false
	}
	d.closeP(pid, true)
	d.events++
	d.calls++
	return 1, true
}

// typeStringOrUntyped renders a type for a refusal text (nil = untyped).
func typeStringOrUntyped(t types.Type) string {
	if t == nil {
		return "untyped"
	}
	return t.String()
}

// unseqCompositeLit classifies a VALUE composite literal (Stage E E4): a named
// struct literal `T{…}` (a pure `struct-lit` head over its payloads), a slice
// literal `[]T{…}` (an `alloc` body — a fresh backing array; NO E1 edge, v2.1
// R3) or — Stage E5 E5c — a map literal (an `alloc` body: the fresh map + its
// entry stores; no E1 edge); every element value is classified (its reads are
// the occurrences), a keyed slice index is a constant. Array literals (arrays
// are outside the type grammar) and elided `&T` elements stay legacy by name.
func (e *emitter) unseqCompositeLit(cl *ast.CompositeLit, ctx *unseqCtx, d *unseqDecision) (unseqExprKind, bool) {
	refuse := func(why string) (unseqExprKind, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return unseqConst, false
	}
	t := e.goTypeOf(cl)
	if t == nil {
		return refuse("composite literal of an untyped kind")
	}
	switch u := types.Unalias(t).Underlying().(type) {
	case *types.Struct:
		if _, isNamed := types.Unalias(t).(*types.Named); !isNamed {
			return refuse("anonymous struct literal")
		}
		if !unseqTypeOK(t) {
			return refuse("struct literal of a type outside the grammar (" + t.String() + ")")
		}
		for _, elt := range cl.Elts {
			v := elt
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				v = kv.Value
			}
			if _, ok := e.unseqValueOrAddr(v, ctx, d); !ok {
				return unseqConst, false
			}
		}
		return unseqValue, true
	case *types.Slice:
		if !unseqTypeOK(u.Elem()) {
			return refuse("slice literal element type outside the grammar (" + u.Elem().String() + ")")
		}
		for _, elt := range cl.Elts {
			v := elt
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				if tv, isConst := e.info.Types[kv.Key]; !isConst || tv.Value == nil {
					return refuse("slice literal key is not constant")
				}
				v = kv.Value
			}
			if _, ok := e.unseqValueOrAddr(v, ctx, d); !ok {
				return unseqConst, false
			}
		}
		return unseqValue, true
	case *types.Map:
		// Stage E5 E5c (2026-09-22): a MAP literal — an `allocate` body (the fresh map + its keyed
		// entry stores) WITHOUT E1 edges (v2.1 R3: a composite literal is not a call); the entries'
		// reads are the occurrences, unordered against the sibling calls. gc realizes the literal
		// at its lexical position (the E13 guard's measured note) — one member of the set. The
		// type grammar's map types only (an int/bool/string key, an admitted value).
		if !unseqTypeOK(t) {
			return refuse("map literal of a type outside the grammar (" + t.String() + ")")
		}
		for _, elt := range cl.Elts {
			kv, ok := elt.(*ast.KeyValueExpr)
			if !ok {
				return refuse("map literal element without a key")
			}
			if _, ok := e.unseqExpr(kv.Key, ctx, d); !ok {
				return unseqConst, false
			}
			if _, ok := e.unseqValueOrAddr(kv.Value, ctx, d); !ok {
				return unseqConst, false
			}
		}
		return unseqValue, true
	case *types.Array:
		return refuse("array literal (arrays are outside the type grammar)")
	case *types.Pointer:
		return refuse("elided &T composite literal element")
	}
	return refuse("composite literal of type " + t.String())
}

// unseqAddrLit classifies `&T{…}` (Stage E E4): a struct literal's payloads,
// then an `alloc new` body binding the fresh pointer (no E1 edge).
func (e *emitter) unseqAddrLit(cl *ast.CompositeLit, ctx *unseqCtx, d *unseqDecision) (unseqExprKind, bool) {
	t := e.goTypeOf(cl)
	if t == nil {
		if d.reason == "" {
			d.reason = "address of an untyped composite literal"
		}
		return unseqConst, false
	}
	if _, isStruct := types.Unalias(t).Underlying().(*types.Struct); !isStruct {
		if d.reason == "" {
			d.reason = "address of a non-struct composite literal (" + t.String() + ")"
		}
		return unseqConst, false
	}
	return e.unseqCompositeLit(cl, ctx, d)
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
	start := d.seq // the occurrence window's start (unseqDecision.occ)
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
				d.occ(start) // the callee VALUE is a mutable read
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
	case *ast.SelectorExpr:
		// Stage E E3: a METHOD CALL on a concrete receiver.
		sig, ok := e.unseqMethodCallee(fn, ctx, d)
		if !ok {
			return nil, false
		}
		return sig, true
	}
	return refuse("callee expression outside the pilot grammar")
}

// unseqMethodCallee classifies `x.M(...)`'s callee (Stage E E3): a non-generic
// method of a named struct type of the main package (never an interface method,
// never a promoted hop, never a method value / expression), with the receiver
// SUB-EVALUATION classified here — the receiver is the invocation's first
// argument: a pointer receiver takes the pointer operand (an atom or an
// occurrence), an addressable variable's address (a frozen `ref`, no read), or
// `*p`'s nil-asserting `addr-of-deref` (an occurrence that may fail); a value
// receiver copies the operand (an address-taken variable's read is the
// occurrence) or dereferences a pointer operand (an occurrence). Returns the
// method's signature WITHOUT the receiver.
func (e *emitter) unseqMethodCallee(sel *ast.SelectorExpr, ctx *unseqCtx, d *unseqDecision) (*types.Signature, bool) {
	start := d.seq // the occurrence window's start (unseqDecision.occ)
	refuse := func(why string) (*types.Signature, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return nil, false
	}
	if _, isQual := e.qualifiedPkgRef(sel); isQual {
		return refuse("qualified function callee (imported source package)")
	}
	seln, isSel := e.info.Selections[sel]
	if !isSel || seln.Kind() != types.MethodVal {
		return refuse("callee expression outside the pilot grammar")
	}
	fn, isFn := seln.Obj().(*types.Func)
	if !isFn {
		return refuse("method callee without a function object")
	}
	if len(seln.Index()) != 1 {
		return refuse("promoted method call (embedded hops)")
	}
	msig, ok := fn.Type().(*types.Signature)
	if !ok || msig.Recv() == nil {
		return refuse("method callee without a receiver")
	}
	if msig.TypeParams().Len() > 0 || msig.RecvTypeParams().Len() > 0 {
		return refuse("generic method callee")
	}
	if fn.Pkg() == nil || !e.isMainPackage(fn.Pkg()) {
		return refuse("method callee outside the main package")
	}
	recvT := e.goTypeOf(sel.X)
	if recvT == nil {
		return refuse("method call on an untyped receiver")
	}
	if _, isIface := types.Unalias(recvT).Underlying().(*types.Interface); isIface {
		return refuse("interface method call (dynamic dispatch has no callee value)")
	}
	// the DECLARED receiver: a named struct or a pointer to one
	declRecv := msig.Recv().Type()
	pointerRecv := false
	if ptr, isPtr := types.Unalias(declRecv).Underlying().(*types.Pointer); isPtr {
		pointerRecv = true
		declRecv = ptr.Elem()
	}
	if !unseqTypeOK(declRecv) {
		return refuse("method receiver type outside the grammar (" + declRecv.String() + ")")
	}
	if _, isNamedStruct := types.Unalias(declRecv).(*types.Named); !isNamedStruct {
		return refuse("method on a non-struct named type (E5)")
	}
	opPtr, opIsPtr := types.Unalias(recvT).Underlying().(*types.Pointer)
	if !unseqTypeOK(recvT) {
		return refuse("method receiver operand type outside the grammar (" + recvT.String() + ")")
	}
	_ = opPtr
	// the receiver sub-evaluation
	if pointerRecv {
		if opIsPtr {
			if _, ok := e.unseqValueOrAddr(sel.X, ctx, d); !ok {
				return nil, false
			}
		} else {
			// the implicit &x: an addressable variable's address (frozen, no read);
			// `(*p).M()` — the nil-asserting address of the dereference, an
			// occurrence that may fail; anything else is outside
			inner := ast.Unparen(sel.X)
			switch x := inner.(type) {
			case *ast.Ident:
				obj := e.info.Uses[x]
				if _, isLocal := e.unseqLocalVar(obj); isLocal {
					if ctx.captured[obj] {
						return refuse("pointer-receiver call on a captured variable (lifted body)")
					}
				} else if _, isPkg := e.isPackageVar(obj); !isPkg {
					return refuse("pointer-receiver call on a non-variable operand")
				}
			case *ast.StarExpr:
				if _, ok := e.unseqExpr(x.X, ctx, d); !ok {
					return nil, false
				}
				d.occ(start) // &*p asserts p non-nil (spec#Address_operators)
			default:
				return refuse("pointer-receiver call on a non-variable operand")
			}
		}
	} else {
		if _, ok := e.unseqExpr(sel.X, ctx, d); !ok {
			return nil, false
		}
		if opIsPtr {
			d.occ(start) // the auto-dereference of the pointer operand (nil check + copy)
		}
	}
	sig, ok := seln.Type().(*types.Signature)
	if !ok {
		return refuse("method callee without a call signature")
	}
	return sig, true
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
	pid := d.openP() // the call / len / cap is an E1 participant enclosing its operand subtree
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
					// Stage E5 E5e: `len(s)` of a STRING — an E1 participant like a slice's
					// (spec#Length_and_capacity; a constant string's len never reaches here).
					if !(id.Name == "len" && isStringType(types.Unalias(at).Underlying())) {
						return refuse(id.Name + " of a non-slice operand (" + at.String() + ")")
					}
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
				d.closeP(pid, false)
				d.events++
				return 1, true
			case "make", "new":
				// Stage E E4: an allocation call — an E1 participant like len/cap.
				return e.unseqMakeNew(c, id.Name, ctx, d, pid)
			case "min", "max":
				// Stage E5 E5a: a pure E1 participant (reading (a)).
				return e.unseqMinMax(c, id.Name, ctx, d, pid)
			case "append":
				// Stage E5 E5a: an EFFECTFUL E1 participant (reading (a)) — a `wide` body.
				return e.unseqAppend(c, ctx, d, pid)
			case "copy":
				return e.unseqCopy(c, ctx, d, pid)
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
		if _, ok := e.unseqValueOrAddr(a, ctx, d); !ok {
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
	d.closeP(pid, true)
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
	start := d.seq // the occurrence window's start (unseqDecision.occ)
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
	d.occ(start) // the target plan (and, for a compound target, its load)
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
	start := d.seq // the occurrence window's start (unseqDecision.occ)
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
			// Stage E5 E5b (2026-09-22): the MULTI-TARGET forms — a tuple assignment, a
			// multi-value call, the comma-ok receive / map lookup / type assertion; every
			// target a phase-1 sibling.
			if st.Tok != token.DEFINE && st.Tok != token.ASSIGN {
				d.form = "compound"
				return refuse("compound assignment arity")
			}
			if !e.unseqMultiAssign(st, ctx, &d) {
				return refuse("multi-target assignment")
			}
			break
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
				if l.Name == "_" {
					// Stage E5 E5b: `_ = e` — the value is evaluated (its occurrences), nothing is stored.
					d.form = "blank-assign"
				} else if _, _, ok := e.unseqVarTarget(l, define, ctx, &d); !ok {
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
			// Stage E5 E5d: a plain identifier target's value rides `then` — `&x` admitted there; a PLANNED
			// target's value is copied into a store cell (a `ref` head the decoder refuses) — `&x` refused by name.
			if _, isPlain := ast.Unparen(st.Lhs[0]).(*ast.Ident); isPlain {
				if _, ok := e.unseqValueOrAddr(st.Rhs[0], ctx, &d); !ok {
					return refuse("right-hand side")
				}
			} else {
				if id, isAddr := unseqAddrOfVar(st.Rhs[0]); isAddr {
					return refuse("address of a variable (" + id.Name + ") as a planned target's value — the store would copy a `ref` head into a cell; E5d admits &x as an argument, a payload, a plain local's or a return's value")
				}
				if _, ok := e.unseqExpr(st.Rhs[0], ctx, &d); !ok {
					return refuse("right-hand side")
				}
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
					d.occ(start) // the compound op itself may fail
				}
			}
			if op == "<<" || op == ">>" {
				if tv, ok := e.info.Types[st.Rhs[0]]; !ok || tv.Value == nil {
					if t := e.goTypeOf(st.Rhs[0]); t != nil {
						if b, isB := types.Unalias(t).Underlying().(*types.Basic); !isB || b.Info()&types.IsUnsigned == 0 {
							d.occ(start)
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
			if _, ok := e.unseqValueOrAddr(r, ctx, &d); !ok {
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
				case "copy":
					// Stage E5 E5a: the statement form of copy — the count discarded.
					d.form = "call-stmt"
					if _, ok := e.unseqCall(call, ctx, &d, 2); !ok {
						return refuse("copy statement")
					}
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
	d.admitted = d.reason == "" && d.calls >= 1 && d.observable()
	if d.reason == "" && !d.admitted {
		if d.calls == 0 {
			d.reason = "no call occurrence (legacy path: nothing with an effect to reorder against)"
		} else if d.nonEvents == 0 {
			d.reason = "no non-event occurrence beside the call(s) (legacy path: every edge forced)"
		} else {
			d.reason = "no occurrence observable against an effectful event (legacy path: every edge forced — Stage E E3 trigger)"
		}
	}
	return d
}

// unseqMultiAssign classifies a MULTI-TARGET assignment (Stage E5 E5b, 2026-09-22):
// a tuple assignment `a, b = e1, e2` (equal arity; blanks allowed), a multi-value
// call `a, b = f()`, or a comma-ok form `v, ok = <-ch` / `m[k]` / `x.(T)` —
// spec#Assignment_statements' two phases: every target's operands and every
// right-hand expression are evaluated «in the usual order» (unordered among
// themselves except as E1 orders the events), the stores left to right. The
// inter-target operand order (inventory E3/E4) is the graph's: the target plans
// are phase-1 SIBLINGS. Every target rides the same store phase — plain variable
// targets beside a PLANNED target become `target` plans on their own address —
// so a package-level target beside a planned one refuses by name (the global
// plan atom is deferred), as does an interface-typed target beside a planned one
// (the store's value would box inside the graph).
func (e *emitter) unseqMultiAssign(st *ast.AssignStmt, ctx *unseqCtx, d *unseqDecision) bool {
	start := d.seq // the occurrence window's start (unseqDecision.occ)
	refuse := func(why string) bool {
		if d.reason == "" {
			d.reason = why
		}
		return false
	}
	define := st.Tok == token.DEFINE
	planned, global, iface := false, false, false
	for _, l := range st.Lhs {
		kind, ok := e.unseqMultiTarget(l, define, ctx, d)
		if !ok {
			return false
		}
		switch kind {
		case "planned":
			planned = true
		case "global":
			global = true
		}
		if kind != "blank" && kind != "planned" {
			if tt := e.assignTargetType(l, define); tt != nil {
				if _, isIface := types.Unalias(tt).Underlying().(*types.Interface); isIface {
					iface = true
				}
			}
		}
	}
	if planned && global {
		return refuse("package-level target beside a planned target in a multi-target assignment (the global plan atom is deferred — E5b)")
	}
	if planned && iface {
		return refuse("interface-typed target beside a planned target in a multi-target assignment (the store's value would box inside the graph)")
	}
	if len(st.Rhs) == 1 && len(st.Lhs) == 2 {
		switch r := ast.Unparen(st.Rhs[0]).(type) {
		case *ast.UnaryExpr:
			if r.Op == token.ARROW {
				// the comma-ok RECEIVE: an EVENT with two results (E3's receive, two binders)
				d.form = "comma-ok"
				ct := e.goTypeOf(r.X)
				if ct == nil || !unseqTypeOK(ct) {
					return refuse("comma-ok receive on a channel type outside the grammar")
				}
				ch, isChan := types.Unalias(ct).Underlying().(*types.Chan)
				if !isChan || ch.Dir() == types.SendOnly {
					return refuse("comma-ok receive on a non-receivable channel")
				}
				rid := d.openP()
				if _, ok := e.unseqExpr(r.X, ctx, d); !ok {
					return false
				}
				d.closeP(rid, true)
				d.events++
				d.calls++
				return true
			}
		case *ast.IndexExpr:
			if _, isMap := e.unseqMapBase(r.X, d); isMap {
				// the comma-ok MAP LOOKUP: ONE mutable read with two results (never fails)
				d.form = "comma-ok"
				if _, ok := e.unseqExpr(r.X, ctx, d); !ok {
					return false
				}
				if _, ok := e.unseqExpr(r.Index, ctx, d); !ok {
					return false
				}
				d.occ(start)
				return true
			}
		case *ast.TypeAssertExpr:
			if r.Type != nil {
				// the comma-ok TYPE ASSERTION: a pure op with two results (never fails)
				d.form = "comma-ok"
				ot := e.goTypeOf(r.X)
				if ot == nil || !unseqTypeOK(ot) {
					return refuse("comma-ok assertion on an operand type outside the grammar")
				}
				if !unseqTypeOK(e.goTypeOf(r.Type)) {
					return refuse("comma-ok assertion to a type outside the grammar")
				}
				if _, ok := e.unseqExpr(r.X, ctx, d); !ok {
					return false
				}
				return true
			}
		}
	}
	if len(st.Rhs) == 1 {
		call, isCall := ast.Unparen(st.Rhs[0]).(*ast.CallExpr)
		if !isCall {
			return refuse("multi-target assignment with a single non-call right-hand side")
		}
		tup, isTup := e.goTypeOf(call).(*types.Tuple)
		if !isTup || tup.Len() != len(st.Lhs) {
			return refuse("multi-value call arity")
		}
		d.form = "multi-call"
		if _, ok := e.unseqCall(call, ctx, d, len(st.Lhs)); !ok {
			return false
		}
		return true
	}
	if len(st.Lhs) != len(st.Rhs) {
		return refuse("assignment arity")
	}
	d.form = "tuple-assign"
	for _, r := range st.Rhs {
		if _, isTup := e.goTypeOf(r).(*types.Tuple); isTup {
			return refuse("multi-value right-hand side")
		}
		// Stage E5 E5d: beside a planned target every value is copied into a store cell — `&x` (a `ref` head)
		// refused by name; otherwise the tuple rides `then` and `&x` is admitted.
		if planned {
			if id, isAddr := unseqAddrOfVar(r); isAddr {
				return refuse("address of a variable (" + id.Name + ") beside a planned target in a multi-target assignment — the store would copy a `ref` head into a cell; E5d admits &x as an argument, a payload, a plain local's or a return's value")
			}
		}
		if _, ok := e.unseqValueOrAddr(r, ctx, d); !ok {
			return false
		}
	}
	return true
}

// unseqMultiTarget classifies one target of a multi-target assignment (E5b):
// "blank", "plain" (a local variable), "global" (a package-level variable) or
// "planned" (a slice element, map element, dereference or field — a FROZEN plan
// whose operand reads are the occurrences).
func (e *emitter) unseqMultiTarget(l ast.Expr, define bool, ctx *unseqCtx, d *unseqDecision) (string, bool) {
	refuse := func(why string) (string, bool) {
		if d.reason == "" {
			d.reason = why
		}
		return "", false
	}
	switch t := ast.Unparen(l).(type) {
	case *ast.Ident:
		if t.Name == "_" {
			return "blank", true
		}
		_, isPkg, ok := e.unseqVarTarget(t, define, ctx, d)
		if !ok {
			return "", false
		}
		if isPkg {
			return "global", true
		}
		return "plain", true
	case *ast.SelectorExpr:
		if define {
			return refuse("define with a selector target")
		}
		if _, isQual := e.unseqQualifiedPackageVar(t); isQual {
			if _, ok := e.unseqQualifiedTarget(t, d); !ok {
				return "", false
			}
			return "global", true
		}
		if !e.unseqFieldTarget(t, ctx, d) {
			return "", false
		}
		return "planned", true
	case *ast.IndexExpr:
		if define {
			return refuse("define with an index target")
		}
		if _, isMap := e.unseqMapBase(t.X, d); isMap {
			if !e.unseqMapTarget(t, ctx, d) {
				return "", false
			}
			return "planned", true
		}
		if !e.unseqElemTarget(t, ctx, d) {
			return "", false
		}
		return "planned", true
	case *ast.StarExpr:
		if define {
			return refuse("define with a dereference target")
		}
		if !e.unseqDerefTarget(t, ctx, d) {
			return "", false
		}
		return "planned", true
	}
	return refuse("assignment target outside the pilot grammar")
}

// unseqReadWriteTarget classifies a compound/IncDec target: a variable
// identifier (an address-taken local's or a package-level variable's load
// is a READ occurrence of a mutable location — Stage E E1 for the latter; a
// private local's target plan is order-transparent), a `pkg.V` qualified
// package-level variable, or a slice element.
func (e *emitter) unseqReadWriteTarget(lv ast.Expr, ctx *unseqCtx, d *unseqDecision) bool {
	start := d.seq // the occurrence window's start (unseqDecision.occ)
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
			d.occ(start) // the load through the target reads a mutable location
		}
		return true
	case *ast.SelectorExpr:
		if _, isQual := e.unseqQualifiedPackageVar(l); !isQual {
			// Stage E E2: a field compound target — the plan (frozen base), the
			// LOAD a mutable read.
			if !e.unseqFieldTarget(l, ctx, d) {
				return false
			}
			d.occ(start)
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
		d.occ(start) // the load of a package-level variable is a mutable read
		return true
	case *ast.IndexExpr:
		if _, isMap := e.unseqMapBase(l.X, d); isMap {
			// Stage E E2: a map compound target — the plan (frozen map VALUE and
			// key VALUE, one identity for the load and the store), the LOAD a
			// mutable read.
			if !e.unseqMapTarget(l, ctx, d) {
				return false
			}
			d.occ(start)
			return true
		}
		return e.unseqElemTarget(l, ctx, d)
	case *ast.StarExpr:
		// Stage E E2: `*p op= e` — the plan freezes the pointer VALUE; the LOAD
		// is a mutable read (nil-checked).
		if !e.unseqDerefTarget(l, ctx, d) {
			return false
		}
		d.occ(start)
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
