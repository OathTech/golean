package main

// BUG-005's THIRD symptom: `mapRange` snapshots the entry array once and
// the iteration frame reads the KEY AND THE VALUE out of that snapshot, so
// an existing entry whose value is written from inside the loop body is
// read STALE by the later iterations. Go reads a value when iteration
// reaches the entry, so the second iteration observes 99.
//
// Deterministic on both sides — both entries start equal and end equal, so
// map-iteration order is irrelevant: Go returns 109, the machine returns
// 20 under every choice stream. A red pin, not a nondet case.

func mapUpdateDuringRange() int {
	m := map[int]int{1: 10, 2: 10}
	sum := 0
	for _, v := range m {
		m[1] = 99
		m[2] = 99
		sum += v
	}
	return sum
}
