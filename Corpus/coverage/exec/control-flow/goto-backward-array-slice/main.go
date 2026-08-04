package main

// A backward goto re-executing `var a [2]int`, with a SLICE of a
// escaping (a[:] — the implicit address of an addressable array): Go's
// fresh array per execution means the two saved slices view different
// backing storage; the hoisted lowering would alias one cell — silent
// wrong answer. The frontend must refuse (fidelity envelope;
// audit-response 2026-08-04: slicing was not covered by the original
// &-on-bare-identifier check). Pins the frontend-export refusal.

func gotoBackwardArraySlice() int {
	var ps [][]int
	i := 0
loop:
	var a [2]int
	a[0] = i
	ps = append(ps, a[:])
	i++
	if i < 2 {
		goto loop
	}
	return ps[0][0]*10 + ps[1][0]
}

func main() {
	gotoBackwardArraySlice()
}
