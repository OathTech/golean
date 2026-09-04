package main

// `slices.Sort` in DEFER and GO position (stdlib-source-2 audit fix round
// F1). The direct call `slices.Sort(s)` in expression-statement position is
// frontend-intercepted onto the `sortSlice` MACHINE OP (integer kinds;
// memo §3 row M retires the op in slice 4). Before the fix the reach walk
// treated EVERY direct call as intercepted (the real generic never marked
// reached) while the emitter intercepted only the ExprStmt shape — so
// `defer slices.Sort(s)` / `go slices.Sort(s)` lowered the real generic
// with `math/bits.Len` pruned off the wire and the machine went `stuck:
// GoCore function not found` where a refusal was owed. Now both shapes
// REFUSE BY NAME (one predicate for walk and emitter: stdlibreach.go
// interceptedLibraryCall); these rows are born red by design and turn
// green when row M lands (the real slices.Sort everywhere). gc: 123 / 3.

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
