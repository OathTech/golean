package main

// KEY-ONLY map range (`for k := range m`), accumulating an
// order-independent fold over the keys. The guardrail for the inductive
// range rule (`proofs/GoLeanProofs/Laws/Range.lean`, `wp_map_iter_inv`):
// its first witness is this shape, deliberately NOT a quorum program.
// The result is independent of iteration order, so the differential is
// stable under the machine's nondeterministic pick.
func rangeMapKeySum() int {
	m := map[int]int{2: 100, 3: 200, 7: 300}
	sum := 0
	for k := range m {
		sum = sum + k
	}
	return sum
}
