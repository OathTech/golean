package main

// Stage E5 of the evaluation-order model v2.1, family E5c (lane core/unseq-stage-e5-0922,
// 2026-09-22): MAP LITERALS as `allocate` bodies WITHOUT E1 edges (v2.1 R3 — spec#Order_of_evaluation
// orders calls, method calls, receives and logical operations; a composite literal is none of
// those; RATIFIED [USER] 2026-09-22 with the `AllocSpec` arm mechanism): the fresh map and its
// keyed entry stores are ONE occurrence, the entries' reads the occurrences spec-unsequenced
// against the sibling calls. gc realizes a map literal at its lexical position — its dynamic
// entries BEFORE a later call (the E13 guard's measured note) — one member of each set.
// References: enumerate.py E5c1/E5c2; the wire Tests/unseq-wire/e5cmaplit.json + native.

func mut(p *int, v int) func() int {
	return func() int { *p = v; return 5 }
}

// map[int]int{1: x}[1] + m() with m writing the captured x (1 → 10, returns 5): the entry's read of x
// before m 1 + 5 = 6 (gc's — the literal at its position), after 10 + 5 = 15. {6, 15}.
func mapLitEntryVsCall() int {
	x := 1
	m := mut(&x, 10)
	return map[int]int{1: x}[1] + m()
}

// map[int]int{k: 1}[7] + m() with m writing the captured k (7 → 1): the KEY's read before m — the
// entry lands at 7, the lookup finds it: 1 + 5 = 6 (gc's); after m — the entry lands at 1, the
// lookup of 7 misses: 0 + 5 = 5. {6, 5}.
func mapLitKeyVsCall() int {
	k := 7
	m := mut(&k, 1)
	return map[int]int{k: 1}[7] + m()
}

// STRICT: constant entries beside a call — the fresh map's read is the only occurrence unordered
// against m (nobody else holds the map): one observation, 1 + 5 = 6.
func mapLitConstControl() int {
	x := 1
	m := mut(&x, 10)
	return map[int]int{7: 1}[7] + m()
}
