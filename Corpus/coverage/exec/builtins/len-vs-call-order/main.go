package main

// The len-vs-CALL forced-point divergence (bug-fix arc triage §3.4;
// slice 6 landed the guardrail, mini-slice A6 the fix — 2026-08-31,
// t1-fidelity-fixes). spec#Order_of_evaluation orders
// "all function calls, method calls, receive operations, and binary
// logical operations" left-to-right when evaluating an expression's
// operands, and spec#Built-in_functions says built-ins "are called
// like any other function" — so in len(ch) + fill(ch) the len operand
// is read BEFORE the call runs. gc agrees (go1.26.5 probe,
// artifacts/probe/slice6a + the slice-5 triage probe): go run → 1.
//
// A6 (BUG-062 fix): the frontend hoists len/cap exactly when an
// ordered event — receive OR call — lexically FOLLOWS it in the same
// sweep (sweepOrderedEventAfter, emit.go), so the chan/slice rows are
// GREEN, in every function shape and inside short-circuit RHS
// normalization too (the short-circuit row). recv-bearing pins the
// receive-bearing shape green BY DESIGN now (pre-A6 it was green by
// accident of the fnHasRecv hoist).
//
// panicky-before-call pins the A6 hoist with a PANICKY operand and
// nothing panicky to its left: hoisting realizes gc's exact order
// (b[j] panics before the call runs) — no refusal owed. The refusal
// SURVIVOR is panicky-between (RED, frontend-export, BY DESIGN): a
// panicky len operand with a spec-UNORDERED panicky operand to its
// LEFT and an ordered event after — hoisting would reorder the two
// panics away from gc's left-to-right point, and realizing that point
// needs the full-statement linearization deliberately not built
// (BUG-032's recorded residual), so it fails closed naming the shape.

func fill(ch chan int) int {
	ch <- 2
	ch <- 3
	return 0
}

func lenVsCallChan() int {
	ch := make(chan int, 4)
	ch <- 1
	return len(ch) + fill(ch) // spec: len first -> 1; wrong order reads 3
}

func growSlice(s *[]int) int {
	*s = append(*s, 9, 9)
	return 0
}

func lenVsCallSlice() int {
	s := []int{1}
	return len(s) + growSlice(&s)*10 // spec: len first -> 1; wrong order reads 3
}

func lenVsCallRecvBearing() int {
	ch := make(chan int, 4)
	ch <- 1
	sink := make(chan int, 1)
	sink <- 5
	v := len(ch) + fill(ch) // fnHasRecv hoists len here: correct by accident
	return v*10 + <-sink    // 1*10 + 5
}

// A6 guardrail: the same len-vs-call order INSIDE a short-circuit RHS
// (calls hoist into the conditional-normalization accumulator there —
// E3 — and pre-A6 len stayed inline, an unpinned silent wrong order).
// gc: len reads 1 pre-fill, so the RHS is true → v=100; final len is 3.
func lenVsCallShortCircuit(k int) int {
	ch := make(chan int, 4)
	ch <- 1
	v := 0
	if k > 0 && len(ch)+fill(ch) == 1 {
		v = 100
	}
	return v*10 + len(ch) // gc: k=1 → 1003, k=0 → 1 (RHS skipped)
}

var w2 int

func wit2(x int) int { w2 = w2*31 + 7; return x }

// A6 guardrail: panicky operand, NOTHING panicky to its left — the
// hoist realizes gc's exact order (b[j]'s index panic fires before
// wit2 runs; w2 stays 0). Pre-A6 this shape was silently wrong in a
// receive-free function (wit2 ran first) and REFUSED in a
// receive-bearing one (BUG-032's function-scoped predicate).
func lenPanickyBeforeCall(j int) (r int) {
	w2 = 0
	b := make([][]int, 0)
	defer func() { recover(); r = w2 }()
	return len(b[j]) + wit2(5) // gc: 0 (panic precedes the call)
}

var w3 int

func wit3(x int) int { w3 = w3*31 + 3; return x }

// The refusal survivor (RED frontend-export BY DESIGN — BUG-032/A6):
// panicky len operand BETWEEN a spec-unordered panicky operand on its
// left (the type assertion) and an ordered call after it. gc realizes
// left-to-right (interface-conversion panic, w3=0, probe
// .tmp-era t1 fix round); the machine refuses rather than reorder.
// NOT called from main: the frontend quarantines the decl.
func lenPanickyBetween(j int) (r int) {
	w3 = 0
	var iv interface{} = "s"
	b := make([][]int, 0)
	defer func() { recover(); r = w3 }()
	return iv.(int) + len(b[j]) + wit3(5) // gc: 0 (assertion panics first)
}

// BUG-082 audit fix round M1 (2026-09-02): the make-hint lowering joins
// the same unordered-panic hoist class. `make(...)` ALWAYS hoists (a
// statement-level allocation), and since BUG-082's fix its hint operand
// hoists with it — so a panicky hint is evaluated ahead of a spec-
// UNORDERED panicky operand to its left. Both points are spec-legal
// (spec#Order_of_evaluation orders only calls/receives/binary-logical);
// gc realizes the interface-conversion panic ("interface conversion:
// interface {} is string, not int"), the machine the hint's index
// panic ("index out of range [5] with length 2"). The A6 guard
// (residualPanicFreeOperand x sweepPanickyInlineBefore) is not wired
// into emitMake — extending it would newly refuse the pre-existing
// make([]T, n) / make(chan T, n) shapes, a separate arc — so this row
// is RED BY DESIGN at stage differential, on BUG-083's Cases line
// (BUG-032 owns the class). NOT called from main: it panics.
func hintPanickyBetween() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(make(map[int]int, t[k]))
}

// FR-28 (2026-09-04, lane fr27-fr28 — closing BUG-083): the A6 guard
// (`hoistReordersPanic` = residualPanicFreeOperand x
// sweepPanickyInlineBefore) is wired into emitMake's size/hint
// operands. `make` always hoists, so a panicky size/hint evaluated
// ahead of a spec-UNORDERED panicky operand to its left was a silent
// wrong answer (hint-panicky-between above: gc's interface-conversion
// panic vs the hoisted hint's index panic); it now REFUSES BY NAME —
// hint-panicky-between flips stage differential -> frontend-export, still
// RED BY DESIGN, and its slice/chan siblings (make-slice-panicky-between,
// make-chan-cap-panicky-between) pin the same refusal. make-index-left
// pins the trade BUG-083 priced: the guard is conservative-syntactic,
// so a LEFT index panic (where gc — hoisting the make too — realizes
// the hint's panic first and the machine MATCHED) refuses as well —
// a visible red, never a guessed order. make-inner-len pins the closed
// residualPanicFreeOperand hole: an INLINE builtin's operand
// (`len(b[j])` as the size) is not a hoisted temp. NOT called from
// main: the frontend quarantines the decls.
func makeSlicePanickyBetween() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(make([]int, t[k]))
}

func makeChanCapPanickyBetween() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + cap(make(chan int, t[k]))
}

func makeIndexLeft() int {
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + len(make(map[int]int, t[k]))
}

func makeInnerLen() int {
	var iv interface{} = "s"
	b := make([][]int, 0)
	j := 3
	return iv.(int) + len(make([]int, len(b[j])))
}

// GREEN controls of the make guard: a panic-FREE hint beside a panicky
// left operand is not the shape (gc and the machine both realize the
// interface-conversion panic); a hint that is a real CALL leaves only
// its temp in the residual — its own panic fires at its hoisted
// position, gc's too (M1 table: `s[i] + len(make(map, boom()))` -> BOOM
// on both sides). Both PASS at stage differential (expected panic).
func makeHintPanicFree() int {
	var iv interface{} = "s"
	n := 2
	return iv.(int) + len(make(map[int]int, n))
}

func boomCall() int { panic("boom-call") }

// A MAP read as the hint (`nm[1]`, non-interface key) has no panic of its
// own (spec#Index_expressions: zero value on a missing key or nil map), so
// it is panic-free to the guard — the M1 table's gAssertVsMapIndexHint,
// green on both sides (gc's interface-conversion panic).
func makeHintMapRead() int {
	var iv interface{} = "s"
	nm := map[int]int{1: 2}
	return iv.(int) + len(make(map[int]int, nm[1]))
}

func makeHintCall() int {
	s := []int{1}
	i := 9
	return s[i] + len(make(map[int]int, boomCall()))
}

// Audit fix round F1 (2026-09-05): the map-read arm admitted key TYPES
// that are statically comparable but CONTAIN an interface (`struct{v
// any}`, `[1]any`) — hashing such a key panics at run time on an
// uncomparable dynamic value (`hash of unhashable type: []int`, the
// maps/array-key-interface-elem-unhashable row's mechanism), so the
// hoisted hint's hash panic ran ahead of gc's interface-conversion panic
// (a WRONG ANSWER), and on the len/cap path (`iv.(int) + len(nm[k]) +
// wit4(5)`) the same hole REGRESSED the A6 refusal main had. The arm now
// asks containsInterface (any interface anywhere in the key type); these
// three rows are RED frontend-export BY NAME, and the generic twin pins
// that a `K comparable` instantiated at `any` refuses (applySubst first)
// while `K = int` lowers (CONV on both sides). NOT called from main.
type anyKey struct{ v any }

func makeHintStructAnyKey() int {
	var iv interface{} = "s"
	nm := map[anyKey]int{}
	k := anyKey{v: []int{1}}
	return iv.(int) + len(make(map[int]int, nm[k]))
}

func makeHintArrayAnyKey() int {
	var iv interface{} = "s"
	nm := map[[1]any]int{}
	k := [1]any{[]int{1}}
	return iv.(int) + len(make(map[int]int, nm[k]))
}

func lenStructAnyKeyLeftAssert() int {
	var iv interface{} = "s"
	nm := map[anyKey][]int{}
	k := anyKey{v: []int{1}}
	return iv.(int) + len(nm[k]) + wit4(5)
}

func makeHintGenericKey[K comparable](nm map[K]int, k K) int {
	var iv interface{} = "s"
	return iv.(int) + len(make(map[int]int, nm[k]))
}

func makeHintGenericAnyKey() int {
	return makeHintGenericKey[any](map[any]int{}, []int{1})
}

func makeHintGenericIntKey() int {
	return makeHintGenericKey[int](map[int]int{1: 2}, 1)
}

// FR-28 nil-deref TRANSPARENCY (the refinement that lowers cedar-go's
// lexer idiom): when BOTH the hoisted operand and every panicky inline
// node to its left can panic ONLY by nil dereference, the two candidate
// panics are the same runtime error and nothing effectful lies between
// them (calls/receives are hoisted), so the order is unobservable and
// the hoist is taken. Pinned on every nil-ness combination: whichever
// side is nil, gc and the machine report the one nil-deref text; with
// neither nil the value. Applies to len/cap (an ordered call after) and
// to make (unconditional hoist) alike.
type cell struct {
	n int
	s []int
}

var w4 int

func wit4(x int) int { w4 = w4*31 + 11; return x }

func lenNilOnly(which int) int {
	var p, q *cell
	if which&1 == 0 {
		p = &cell{n: 1}
	}
	if which&2 == 0 {
		q = &cell{s: []int{7, 8, 9}}
	}
	w4 = 0
	return b2i(p.n < len(q.s) && wit4(5) > 0)*10 + w4%7 // none nil: 10 + 4
}

func makeNilOnly(which int) int {
	var p, q *cell
	if which&1 == 0 {
		p = &cell{n: 5}
	}
	if which&2 == 0 {
		q = &cell{n: 3}
	}
	return p.n + len(make([]int, q.n)) // none nil: 8
}

// The cedar-go lexer idiom itself (x/exp/schema/internal/parser
// token.go:119 `for l.pos < len(l.src) && l.peek() != '\n'`): a pointer
// receiver's field on the left, `len` of another of its fields, a method
// call after — refused before this refinement (the census §11 FR-28
// witness), GREEN now.
type lexer struct {
	src []byte
	pos int
}

func (l *lexer) peek() byte { return l.src[l.pos] }

func lexerIdiom() int {
	l := &lexer{src: []byte("ab\ncd")}
	for l.pos < len(l.src) && l.peek() != '\n' {
		l.pos++
	}
	return l.pos // 2
}

// The refinement is nil-deref ONLY: an assertion or an index on either
// side keeps the refusal (RED frontend-export BY DESIGN). NOT called
// from main.
func lenAssertVsNilOperand() int {
	var iv interface{} = "s"
	p := &cell{s: []int{1}}
	return iv.(int) + len(p.s) + wit4(5)
}

func lenNilLeftVsIndexOperand() int {
	p := &cell{n: 1}
	b := make([][]int, 0)
	j := 3
	return p.n + len(b[j]) + wit4(5)
}

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

func main() {
	lenVsCallChan()
	lenVsCallSlice()
	lenVsCallRecvBearing()
	lenVsCallShortCircuit(1)
	lenPanickyBeforeCall(3)
	lenNilOnly(0)
	makeNilOnly(0)
	lexerIdiom()
	_ = makeHintGenericIntKey
}
