package main

// NaN as a map key (floats design note 2026-08-04 §4): NaN != NaN under
// Go's ==, so every insert with a NaN key appends a DISTINCT entry, and
// lookups/deletes of a NaN key find nothing. Pins the map-key identity
// path (valueEq at the key type) against the IEEE .float equality arm.
func floatNaNMapKey() int {
	zero := 0.0
	nan := zero / zero // runtime 0/0: NaN, never a panic (design note §3.2)
	m := map[float64]int{}
	m[nan] = 1
	m[nan] = 2
	score := len(m) * 100 // two distinct entries
	if _, ok := m[nan]; !ok {
		score += 10 // lookup misses both
	}
	delete(m, nan) // deletes nothing
	score += len(m)
	return score
}

func main() {
	floatNaNMapKey()
}
