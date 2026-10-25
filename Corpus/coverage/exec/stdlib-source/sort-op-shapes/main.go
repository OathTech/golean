package main

// `slices.Sort` in DEFER and GO position (stdlib-source-2 audit fix round
// F1). History: the direct call `slices.Sort(s)` in expression-statement
// position was frontend-intercepted onto the `sortSlice` MACHINE OP
// (integer kinds), and before the fix the reach walk treated EVERY direct
// call as intercepted (the real generic never marked reached) while the
// emitter intercepted only the ExprStmt shape — so `defer slices.Sort(s)` /
// `go slices.Sort(s)` lowered the real generic with `math/bits.Len` pruned
// off the wire and the machine went `stuck: GoCore function not found`
// where a refusal was owed. F1 made both shapes REFUSE BY NAME (born red by
// design); they turned GREEN 2026-09-04 (lane fr4-rowm) when memo §3 row M
// retired the op's intercept. Since 2026-10-25 (backlog row 50, lane
// frontend/g19-sort-intercept-1025) the intercept is BACK for the direct
// integer-kind call, and these rows pin that the `defer`/`go` shapes stay
// the real generic — the reach walk excludes a defer/go statement's own
// call from the intercept (stdlibreach.go spawnCalls), so the deferred/
// spawned function value is the real `slices.Sort[[]int,int]` with
// `pdqsortOrdered`/`math/bits.Len` on the wire; the F1 refusal is retired,
// not revived. gc: 123 / 3.

import "slices"

func deferSort() (out int) {
	s := []int{3, 1, 2}
	defer func() { out = s[0]*100 + s[1]*10 + s[2] }() // runs AFTER the deferred sort (LIFO)
	defer slices.Sort(s)
	return
}

func goSort() int {
	s := []int{3, 1, 2}
	go slices.Sort(s) // no completion signal; only len (unwritten by Sort) is observed
	return len(s)
}

func main() {
	println(deferSort())
	println(goSort())
}
