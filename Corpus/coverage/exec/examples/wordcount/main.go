package main

import "fmt"

func maxCount(words []uint64) uint64 {
	counts := make(map[uint64]uint64)
	for i := 0; i < len(words); i++ {
		counts[words[i]]++
	}
	best := uint64(0)
	for _, c := range counts {
		if c > best {
			best = c
		}
	}
	return best
}

func maxCountFour(a, b, c, d uint64) uint64 {
	return maxCount([]uint64{a, b, c, d})
}

func maxCountOne(a uint64) uint64 {
	return maxCount([]uint64{a})
}

func maxCountEmpty() uint64 {
	return maxCount([]uint64{})
}

// wordcount_harness: three-phase harness — setup builds the word
// family w[i] = seed + i%3 (controllable multiplicities); the
// returned max count is the observable (returned data).
func wordcount_harness(n, seed uint64) uint64 {
	w := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		w[i] = seed + i%3
	}
	return maxCount(w)
}

// wordcountCapN: the fixed observation cap of the S3 relational
// harness. The returned array is `[wordcountCapN]uint64`, so the
// harness's own bound is `n <= 8` — plainly visible in the source, and
// the future Lean headline carries it as a hypothesis.
const wordcountCapN = 8

// wordcount_harness_r: the S3 RELATIONAL harness (examples phase-2
// slice 1, 2026-08-14; scoping study §4.7, re-landed by slice 1.5
// after the `wc_empty_run` cost blocker was retired). Returns the
// WORDS (as a fixed-cap array, the pass-by-value fragment's
// unbounded-data workaround) alongside the subject's answer, so the
// Lean postcondition relates the returned data DIRECTLY —
// `best = maxMultiplicity words` — with no family function
// re-describing the setup. Real Go, ghost ladder rung 0.
func wordcount_harness_r(n, seed uint64) ([wordcountCapN]uint64, uint64) {
	w := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		w[i] = seed + i%3
	}
	var words [wordcountCapN]uint64
	for i := uint64(0); i < n; i++ {
		words[i] = w[i]
	}
	best := maxCount(w)
	return words, best
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", maxCountFour(7, 3, 7, 7))
}
