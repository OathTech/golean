package main

// A backward goto re-executing `var a [2]int`, with the address of an
// ELEMENT of a escaping through a parenthesized operand (&(a[0])): Go
// re-executes the declaration on each backward jump, giving a fresh
// array, so the saved pointers refer to different cells; the hoisted
// lowering would alias one cell — silent wrong answer. The frontend
// must refuse (fidelity envelope; audit-response 2026-08-04: ParenExpr
// and IndexExpr chains defeated the original bare-identifier check).
// This case pins the visible frontend-export refusal.

func gotoBackwardElemAddr() int {
	var ps []*int
	i := 0
loop:
	var a [2]int
	a[0] = i
	ps = append(ps, &(a[0]))
	i++
	if i < 2 {
		goto loop
	}
	return *ps[0]*10 + *ps[1]
}

func main() {
	gotoBackwardElemAddr()
}
