package main

// BUG-088 pin (design-hygiene arc slice 1, B1 entry-identity stamps,
// 2026-09-03): a range over a map whose keys are NaN. Each NaN insert is
// a DISTINCT entry (NaN != NaN), and spec#For_statements' production
// table produces every entry exactly once, so gc prints 32 (sum 1+2,
// two entries) under every iteration order. The retired KEY-set frame
// could never mark a NaN entry produced (`produced` membership was Go
// map-key equality, irreflexive on NaN), so the canonical zero-stream
// run re-produced the first entry forever and fueled out; the stamped
// frame marks the ENTRY produced and terminates. Schedule-confluent:
// both orders sum to 3. (NaN is built by division so the row stays on
// the modeled frontier — `math.NaN()` is frontend-quarantined.)
func nanKeyRange() int {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{}
	m[nan] = 1
	m[nan] = 2
	sum := 0
	for _, v := range m {
		sum += v
	}
	return sum*10 + len(m)
}

func main() {
	println(nanKeyRange())
}
