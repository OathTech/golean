package main

import "fmt"

func bubbleSort(s []uint64) {
	for end := len(s); end > 1; end-- {
		swapped := false
		for i := 1; i < end; i++ {
			if s[i-1] > s[i] {
				s[i-1], s[i] = s[i], s[i-1]
				swapped = true
			}
		}
		if !swapped {
			return
		}
	}
}

func sortFour(a, b, c, d uint64) (uint64, uint64, uint64, uint64) {
	s := []uint64{a, b, c, d}
	bubbleSort(s)
	return s[0], s[1], s[2], s[3]
}

func sortThree(a, b, c uint64) (uint64, uint64, uint64) {
	s := []uint64{a, b, c}
	bubbleSort(s)
	return s[0], s[1], s[2]
}

func sortOne(a uint64) uint64 {
	s := []uint64{a}
	bubbleSort(s)
	return s[0]
}

func sortEmpty() int {
	s := []uint64{}
	bubbleSort(s)
	return len(s)
}

// bubbleCapN: the fixed observation cap of the S3 relational harness.
// Both returned arrays are `[bubbleCapN]uint64`, so the harness's own
// bound is `n <= 8` — plainly visible in the source.
const bubbleCapN = 8

// bubble_harness_r: the S3 RELATIONAL harness. Setup builds a
// genuinely-unsorted family by iterating a wrapping LCG from `seed`;
// a copy loop lifts it into `pre` (the fixed-cap array is the
// pass-by-value fragment's unbounded-data workaround), the subject
// sorts in place, and a second copy loop lifts the result into
// `post`, so a postcondition can relate the returned data directly.
// Real Go, ghost ladder rung 0.
func bubble_harness_r(n, seed uint64) ([bubbleCapN]uint64, [bubbleCapN]uint64) {
	s := make([]uint64, n)
	x := seed
	for i := uint64(0); i < n; i++ {
		x = x*2862933555777941757 + 3037000493
		s[i] = x
	}
	var pre [bubbleCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	bubbleSort(s)
	var post [bubbleCapN]uint64
	for i := uint64(0); i < n; i++ {
		post[i] = s[i]
	}
	return pre, post
}

func main() {
	a, b, c, d := sortFour(4, 2, 3, 1)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a, b, c, d,
	)
}
