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

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", maxCountFour(7, 3, 7, 7))
}
