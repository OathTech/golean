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

func main() {
	lenVsCallChan()
	lenVsCallSlice()
	lenVsCallRecvBearing()
	lenVsCallShortCircuit(1)
	lenPanickyBeforeCall(3)
}
