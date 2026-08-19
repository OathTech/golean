package main

// BUG-005 probe (bug-fix arc slice 4, 2026-08-19): the re-created-key axis
// none of the three BUG-005 reds touch. Each iteration deletes the CURRENT
// key and immediately re-adds it — a re-created entry is "created during
// iteration", so the spec's added-entries latitude LITERALLY admits
// re-producing it; gc never does (probe C/D, artifacts/probe/map005:
// n=3 in 400/400 plain runs and 400/400 runs with forced mid-iteration
// growth and shrink). The subject pins the BOUNDED envelope member both
// models realize — every key produced at least once, none more than
// a small bound, loop terminates — returning the exact count so a fix that
// introduces unbounded re-production (the literal-latitude trap recorded
// in the slice-4 memo's envelope statement) goes visibly red rather than
// silently diverging.

func mapDeleteReAddDuringRange() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
	for k := range m {
		n++
		if n > 50 {
			return -1 // runaway guard: outside any honest envelope
		}
		delete(m, k)
		m[k] = k
	}
	return n
}

func main() {
	println(mapDeleteReAddDuringRange())
}
