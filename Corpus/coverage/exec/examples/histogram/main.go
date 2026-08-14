package main

import "fmt"

// histogram: build a count map over the values, then report two
// summaries — how many times the queried value `q` occurs, and how many
// distinct values the histogram holds. The distinct count RANGES over
// the map, so its iteration order is nondeterministic; the summary is
// order-invariant by construction.
func histogram(vals []uint64, q uint64) (uint64, uint64) {
	counts := make(map[uint64]uint64)
	for i := 0; i < len(vals); i++ {
		counts[vals[i]]++
	}
	hits := counts[q]
	distinct := uint64(0)
	for range counts {
		distinct++
	}
	return hits, distinct
}

func histogramFour(a, b, c, d, q uint64) (uint64, uint64) {
	return histogram([]uint64{a, b, c, d}, q)
}

func histogramOne(a, q uint64) (uint64, uint64) {
	return histogram([]uint64{a}, q)
}

func histogramEmpty(q uint64) (uint64, uint64) {
	return histogram([]uint64{}, q)
}

// histogramCapN: the fixed observation cap of the S3 relational
// harness. The returned array is `[histogramCapN]uint64`, so the
// harness's own bound is `n <= 8` — plainly visible in the source, and
// the Lean headline carries it as a hypothesis.
const histogramCapN = 8

// histogram_harness_r: the S3 RELATIONAL harness (gallery campaign G1,
// 2026-08-15). Setup builds the value family v[i] = seed + i%3
// (controllable multiplicities); the harness returns the VALUES it
// counted (as a fixed-cap array, the pass-by-value fragment's
// unbounded-data workaround) alongside both summaries, so the Lean
// postcondition relates the returned data DIRECTLY — no family function
// re-describing the setup. Real Go, ghost ladder rung 0.
func histogram_harness_r(n, seed, q uint64) ([histogramCapN]uint64, uint64, uint64) {
	v := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		v[i] = seed + i%3
	}
	var vals [histogramCapN]uint64
	for i := uint64(0); i < n; i++ {
		vals[i] = v[i]
	}
	hits, distinct := histogram(v, q)
	return vals, hits, distinct
}

func main() {
	hits, distinct := histogramFour(7, 3, 7, 7, 7)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		hits, distinct,
	)
}
