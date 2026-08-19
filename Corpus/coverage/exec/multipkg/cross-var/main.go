package main

// Multi-package guardrail (raft W1.1, 2026-08-18): cross-package
// package-level VARIABLES — read, write, compound assign, and address
// aliasing. A qualified `store.V` is NAME RESOLUTION to the seeded
// global cell (identity note §1), never field selection: the write
// must land in the same cell the owning package's own code and the
// &-alias observe.

import "store"

func crossVarStore() int {
	store.Counter = 40
	store.Counter += 2
	p := &store.Counter
	*p += 100
	// Sequenced reads (no mutating call beside an unsequenced read —
	// that order is spec latitude, not a differential target).
	a := store.Counter * 10
	b := store.Bump()
	return a + b
}

func main() {}
