package main

// NaN map keys are unreachable by lookup/delete (NaN != NaN) but
// `clear` removes them: the one builtin that reaches entries no key
// expression can name. Complements floats/nan-map-key (insert /
// lookup-miss / delete-miss) with the clear cell. Green cell from the
// external Codex review 2026-08-08
// (docs/2026-08-08_semantic-divergence-review.md §2).

func nanKeyClear() int {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{}
	m[nan] = 1
	m[nan] = 2 // second DISTINCT entry
	before := len(m)
	clear(m)
	return before*10 + len(m) // 20: two entries, then none
}

func main() {
	nanKeyClear()
}
