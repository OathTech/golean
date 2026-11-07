package main

// E2GFLD (Stage E, family E2 — the train-31 pre-merge audit's finding D, lane
// frontend/fix-e7-cut-1107, 2026-11-07): the FIELD of a PACKAGE-LEVEL struct variable read
// beside a call that writes it. The emitter spells `v.n` as a field read over the global's own
// read, `field-get(deref(globaladdr v))` — the E1 family's admitted pointer position under the
// E2 head — and the fragment refused the receiver as a non-atom pointer, so the whole wire was
// refused by name (status error) where gc runs it. The read of v.n is spec-unsequenced against
// mut's call: {0, 500}; gc 500 (call-first) on the plain argument.
type V struct{ n int }
type P struct{ a, b int }

var v V

func sink(a, k int) int        { return a*100 + k }
func sinkAny(x any, k int) int { return x.(P).a*100 + k }

func e2gfld() int {
	mut := func() int { v.n = 5; return 0 }
	return sink(v.n, mut())
}

// E2GFLDLIT: the same read inside a struct literal boxed into `any` — the auditor's program. The
// boxed literal is a needsaddr operand gc's order pass copies at its position (finding B's class),
// so gc answers 0 (the read before mut); the machine's set holds both: {0, 500}.
func e2gfldlit() int {
	mut := func() int { v.n = 5; return 0 }
	return sinkAny(P{v.n, 0}, mut())
}

func main() { println(e2gfld(), e2gfldlit()) }
