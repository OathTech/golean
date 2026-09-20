package main

// The native `unseq` PILOT rows (evaluation-order model v2.1 Stage C, lane
// core/unseq-stage-c-0919, 2026-09-19; design docs/2026-09-19_unseq-stage-c-design.md):
// the v2.1 spike's witnesses W1/W2/W3/W5/W6, R1, R2a-c, R4, R6
// (docs/evidence/2026-09-16_eval-order-v2-spike/outcomes.txt) written as ordinary Go
// and lowered by the REAL frontend as `unseq` graphs — check (b) «machine equals
// reference over the wire» on the LOWERED graphs, with gc sampled into the sets.
// Each sweep puts a spec-UNSEQUENCED pair in one statement: a read of a
// CAPTURED local or a slice element (a mutable location) beside a call that
// mutates it (spec#Order_of_evaluation: «the order of those events compared to
// the evaluation and indexing of x and the evaluation of y and z is not
// specified»); the machine's ONE consumption site is the `unseq` scheduler's
// pick (`unseqNext`, bound = the ready-set size); gc realizes call-first
// (E12's pin) on every row and its draw lies in every set. W4 (no call) is a
// hand-built wire only (Tests/unseq-wire) — the emitter's trigger admits no
// call-free sweep. Subjects return a checksum where the reference observes an
// output, so every `ok` row carries a value.

// W1: v := mut() + a, a captured. {1, 2}; gc 2.
func w1() int {
	a := 1
	mut := func() int { a = 2; return 0 }
	v := mut() + a
	return v
}

// W2: v := a[b[0]] + mut(), a and b captured. {10, 30, 40}; gc 40.
func w2() int {
	a := make([]int, 2)
	b := make([]int, 1)
	a[0] = 10
	a[1] = 20
	b[0] = 0
	mut := func() int { a[0] = 30; a[1] = 40; b[0] = 1; return 0 }
	v := a[b[0]] + mut()
	return v
}

// W3: a[i] += mut() with mut setting i = 1 and returning 1 — ONE frozen target
// identity for the load and the store. {"w3 11 20" → 1120, "w3 10 21" → 1021};
// the hybrid "w3 10 11" absent; gc 1021.
func w3() int {
	a := make([]int, 2)
	a[0] = 10
	a[1] = 20
	i := 0
	mut := func() int { i = 1; return 1 }
	a[i] += mut()
	println("w3", a[0], a[1])
	return a[0]*100 + a[1]
}

// W5: println(a[0] + mut()) twice in a loop, mut nils a — per-activation cells:
// the panic at iteration 0 with nothing printed, or "7" then the panic at
// iteration 1; never a completed second iteration. gc: the panic at once.
func w5() {
	a := make([]int, 1)
	a[0] = 7
	mut := func() int { a = nil; return 0 }
	n := 0
	for n < 2 {
		println(a[0] + mut())
		n++
	}
}

// W6: v := x + inc() + inc(), x captured. {0, 1, 2}; gc 2.
func w6() int {
	x := 0
	inc := func() int { x++; return 0 }
	v := x + inc() + inc()
	return v
}

// R1: v := x + y + mut(), both captured — the unreduced set {0, 1, 2, 3}
// (the read-order reduction the second review refuted would lose 1); gc 3.
func r1() int {
	x, y := 0, 0
	mut := func() int { x = 1; y = 2; return 0 }
	v := x + y + mut()
	return v
}

func h() bool                    { println("guard h"); return true }
func k() int                     { println("guard k"); return 7 }
func sinkB(b bool, n int)        { println("guard result", b, n) }
func sinkL(b bool, n int)        { println("logical", b, n) }
func sink3(g int, c bool, k int) { println("sink", g, c, k) }

// R2a, z true: the skipped region discharges the E1 edge k follows — a singleton
// (strict): "guard k / guard result true 7".
func r2aTrue() int {
	z := true
	sinkB(z || h(), k())
	return 1
}

// R2a, z false: h runs before k (E1 through the completion) — a singleton (strict).
func r2aFalse() int {
	z := false
	sinkB(z || h(), k())
	return 1
}

// R2b: sinkL(left || b, change()) — the || is anchored at its COMPLETION, so
// change() (which sets b) runs after the right operand's read: "logical false 0",
// a singleton (strict). Anchored at the entry it would be {false, true}.
func r2b() int {
	left := false
	b := false
	change := func() int { b = true; return 0 }
	sinkL(left || b, change())
	return 1
}

// R2c: sink3(g(), a || (b && h2()), k2()) — nested guards, g (which sets a) before
// the || entry, k2 after its completion. b true: {"g k", "g h k"}; b false: {"g k
// sink 1 true 7", "g k sink 1 false 7"}; gc "g k sink 1 true 7" in both.
func r2cTrue() int {
	a := false
	b := true
	g := func() int { println("g"); a = true; return 1 }
	h2 := func() bool { println("h"); return true }
	k2 := func() int { println("k"); return 7 }
	sink3(g(), a || (b && h2()), k2())
	return 1
}

func r2cFalse() int {
	a := false
	b := false
	g := func() int { println("g"); a = true; return 1 }
	h2 := func() bool { println("h"); return true }
	k2 := func() int { println("k"); return 7 }
	sink3(g(), a || (b && h2()), k2())
	return 1
}

// R4: old := a; a[0] += mut() with mut REBINDING a to b — the frozen header keeps
// one identity: {"old 11 20 / a 100 200", "old 10 20 / a 101 200"}; the hybrids
// "old 10 20 / a 11 200" and "old 101 20 / a 100 200" absent; gc the second.
func r4() int {
	a := make([]int, 2)
	a[0] = 10
	a[1] = 20
	b := make([]int, 2)
	b[0] = 100
	b[1] = 200
	old := a
	mut := func() int { a = b; return 1 }
	a[0] += mut()
	println("old", old[0], old[1])
	println("a", a[0], a[1])
	return old[0]*1000 + a[0]
}

// R6: v := a[f()] with f rebinding a — the header producer SPLIT from the checked
// access (ruling (4)): {10, 20}; gc 20. A fused read would be {20} alone.
func r6() int {
	a := make([]int, 1)
	a[0] = 10
	b := make([]int, 1)
	b[0] = 20
	f := func() int { a = b; return 0 }
	v := a[f()]
	return v
}

func main() {
	println(w1(), w2(), w3(), w6(), r1(), r2aTrue(), r2aFalse(), r2b(), r2cTrue(), r2cFalse(), r4(), r6())
	w5()
}
