package main

// Round-4 pins (BUG-033): a target's address CHAIN — every indexAddr/
// fieldAddr step from the anchor outward — is ONE phase-2 address
// computation in gc: its bounds/nil checks fire AT THE STORE, after
// earlier targets' stores landed. Deferring only the OUTERMOST step
// (the round-3 targetPlan) fires an inner index check in phase 1 and
// loses the earlier store. The boundary is probed, not guessed:
// a VALUE step in the base (an inner SLICE element, index-GET) is an
// operand and stays phase 1 — the inner-value-guard below pins the
// contrast direction.

type cT struct{ f int }

func chainTwo(fn func()) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	fn()
	return 0
}

func chainFieldOverIndex() int {
	a := []cT{}
	x := 0
	hit := chainTwo(func() { x, a[9].f = 1, 7 })
	return hit*100 + x*5
}

func chainNilSliceField() int {
	var a []cT
	x := 0
	hit := chainTwo(func() { x, a[0].f = 1, 7 })
	return hit*100 + x*5
}

func chainArrayField() int {
	var arr [1]cT
	i := 3
	x := 0
	hit := chainTwo(func() { x, arr[i].f = 1, 7 })
	return hit*100 + x*5
}

func chainArrayNested() int {
	var arr [2][3]int
	j := 9
	x := 0
	hit := chainTwo(func() { x, arr[1][j] = 1, 7 })
	return hit*100 + x*5
}

// CONTRAST GUARD (stays green): on [][]int the inner element is a
// slice VALUE — an index-expression OPERAND, evaluated (and
// bounds-checked) in phase 1, BEFORE any store. gc: x stays 0.
func chainInnerValueGuard() int {
	aa := [][]int{}
	x := 0
	hit := chainTwo(func() { x, aa[9][0] = 1, 7 })
	return hit*100 + x*5
}

func main() {
	chainFieldOverIndex()
}
