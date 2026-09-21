package main

// Stage E of the evaluation-order model v2.1, family E1 (lane core/unseq-stage-e-0921,
// 2026-09-21): PACKAGE-LEVEL VARIABLES as occurrences. The width-of-P ruling ([USER] Mike
// 2026-09-19, relayed: «ALL mutable reads, STAGED») reaches the first kind beyond the
// Stage C pilot's captured locals and slice elements: a package-level variable is a
// mutable location, so its read beside a call is a READ occurrence spec-unsequenced
// against the call (spec#Order_of_evaluation: «the order of those events compared to the
// evaluation and indexing of x and the evaluation of y and z is not specified»); as a
// compound target its identity has no operands, so the store lands in phase 2 and the
// load is the same READ occurrence. The reference sets are enumerate.py's E1a/E1c
// (docs/evidence/2026-09-16_eval-order-v2-spike/outcomes.txt); the hand-built and native
// wires Tests/unseq-wire/{e1,e1c}.json certify them over the wire; these rows sample gc
// into them (gc realizes call-first — E12's pin — on every row). BUG-113's rows
// (evalorder/legacy-logical-vs-call) are this family's wrong-answer fix and stay there.

var g = 1
var h = 1

func setG() int { g = 10; return 1 }

func wit(x int) int { println("wit", x); return x }

// E1a: v := mut() + g, mut writes g (g = 2). {1, 2}; gc 2 (call-first).
func readVsCall() int {
	mut := func() int { g = 2; return 0 }
	v := mut() + g
	return v
}

// E1c: g += setG() with setG writing g = 10 and returning 1 — the compound target's load
// is the read occurrence, the store rides phase 2: read before the call → 1 + 1 = 2
// (overwriting the 10), after → 10 + 1 = 11 (gc's). {2, 11}.
func compoundVsCall() int {
	g = 1
	g += setG()
	return g
}

// A global read beside a call that does NOT touch it: both orders give the same value —
// a strict singleton with one wide pick (the read vs the call), covered by the streams.
func readVsUnrelatedCall() int {
	return h + wit(1)
}

// g = f(): a plain package-level target has no operands and the sweep carries no
// non-event occurrence — it stays on the legacy path by the trigger (a control).
func plainTargetCall() int {
	g = 1
	g = wit(1) + 1
	return g
}

func main() {
	println(readVsCall())
	println(compoundVsCall())
	println(readVsUnrelatedCall())
	println(plainTargetCall())
}
