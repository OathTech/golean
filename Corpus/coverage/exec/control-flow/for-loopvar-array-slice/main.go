package main

// Go >= 1.22 per-iteration loop variables, escaping via the IMPLICIT
// ADDRESS taken when slicing an addressable array (a[:] is (&a)[:]):
// each iteration's array cell is distinct, so the saved slices view
// 0,1,2. The per-iteration trigger detected only func-literal captures,
// so this escape took the shared-cell lowering — silent wrong answer,
// Lean 333 vs Go 12 (delta-review round 2, 2026-08-04).
func forLoopvarArraySlice() int {
	var ss [][]int
	for a := [1]int{}; a[0] < 3; a[0]++ {
		ss = append(ss, a[:])
	}
	return ss[0][0]*100 + ss[1][0]*10 + ss[2][0]
}

func main() {
	forLoopvarArraySlice()
}
