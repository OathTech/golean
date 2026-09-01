package main

// The min/max-vs-CALL forced-point divergence — grossmith campaign 2's
// F-1/F-2 (docs/2026-08-20_grossmith-findings-2.md §1), promoted to
// corpus pins by the launch-audit fix round (V1 re-reproduced all five
// colors independently at 5f5642eb). Same spec ground as the sibling
// len-vs-call-order family: spec#Order_of_evaluation orders function
// calls left-to-right, and spec#Built-in_functions says built-ins "are
// called like any other function" — so min/max are ORDERED events and
// their operands evaluate before a lexically later call runs. Pre-A6
// the frontend's ordered-event predicate omitted the value-returning
// built-ins (BUG-062's widened statement) and the machine ran the
// later call first.
//
// ALL FIVE GREEN since mini-slice A6 (2026-08-31, t1-fidelity-fixes):
// min/max hoist exactly when an ordered event follows in the same
// sweep (sweepOrderedEventAfter, emit.go), like any other call;
// append-arg-panic and call-in-builtin-arg pin that append's standing
// ordering and arg-list call hoists did not regress.

var w int

func wit(x int, tag int) int { w = w*31 + tag; return x }

// min is the lexically first CALL; wit is the second. min must be
// called before wit, and min cannot be called before its arguments are
// evaluated — so s[i] panics BEFORE wit runs, and w is 0.
func probeBuiltinArgIndex() (r int) {
	w = 0
	s := "abc"
	i := 100
	defer func() { recover(); r = w }()
	var a byte
	var b int
	a, b = min(byte(1), s[i]), wit(7, 9)
	_, _ = a, b
	return -1 // gc: 0 (panic precedes wit); wrong order: 9
}

var n int

func bump() int { n = 5; return 0 }

// min is called before bump, and min reads n before it is called:
// the spec-forced answer is 1. Silent wrong answer otherwise.
func probeMinValueOrder() int {
	n = 1
	return min(n, 100) + bump() // gc: 1; wrong order: 5
}

func probeMaxValueOrder() int {
	n = 1
	return max(n, -100) + bump() // gc: 1; wrong order: 5
}

var b1 int

func witB1a(x int) int { b1 = b1*31 + 1; return x }
func witB1b(x int) int { b1 = b1*31 + 2; return x }

// GREEN control: a user CALL inside a built-in's argument list. The
// frontend already hoists these in lexical order — min's arg call
// runs before the later call, so b1=1*31+2=33 on both sides.
func probeCallInsideBuiltinArg() int {
	b1 = 0
	_, _ = min(1, witB1a(5)), witB1b(6)
	return b1 // 33 on gc AND on the machine
}

var b3 int

func witB3(x int, tag int) int { b3 = b3*31 + tag; return x }

// GREEN control: append is ALREADY an ordered event, so its operand's
// panic precedes the later call. A6 must not regress this to the
// min/max behaviour.
func probeAppendArgIndex() (r int) {
	b3 = 0
	s := "abc"
	i := 100
	xs := []byte{1}
	defer func() { recover(); r = b3 }()
	var a []byte
	var b int
	a, b = append(xs, s[i]), witB3(7, 9)
	_, _ = a, b
	return -1 // gc: 0 (panic precedes witB3); regression would read 9
}

func main() {
	probeBuiltinArgIndex()
	probeMinValueOrder()
	probeMaxValueOrder()
	probeCallInsideBuiltinArg()
	probeAppendArgIndex()
}
