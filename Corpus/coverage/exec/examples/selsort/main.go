package main

import "fmt"

func selectionSort(s []uint64) {
	for i := 0; i < len(s); i++ {
		m := i
		for j := i + 1; j < len(s); j++ {
			if s[j] < s[m] {
				m = j
			}
		}
		s[i], s[m] = s[m], s[i]
	}
}

func sortFour(a, b, c, d uint64) (uint64, uint64, uint64, uint64) {
	s := []uint64{a, b, c, d}
	selectionSort(s)
	return s[0], s[1], s[2], s[3]
}

func sortThree(a, b, c uint64) (uint64, uint64, uint64) {
	s := []uint64{a, b, c}
	selectionSort(s)
	return s[0], s[1], s[2]
}

func sortOne(a uint64) uint64 {
	s := []uint64{a}
	selectionSort(s)
	return s[0]
}

func sortEmpty() int {
	s := []uint64{}
	selectionSort(s)
	return len(s)
}

// selsortCapN: the fixed observation cap of the S3 relational harness.
// Both returned arrays are `[selsortCapN]uint64`, so the harness's own
// bound is `n <= 8` — plainly visible in the source.
const selsortCapN = 8

// selsort_harness_r: the S3 RELATIONAL harness. Setup builds a
// genuinely-unsorted family by iterating a wrapping LCG from `seed`;
// a copy loop lifts it into `pre` (the fixed-cap array is the
// pass-by-value fragment's unbounded-data workaround), the subject
// sorts in place, and a second copy loop lifts the result into
// `post`, so a postcondition can relate the returned data directly.
// Real Go, ghost ladder rung 0.
func selsort_harness_r(n, seed uint64) ([selsortCapN]uint64, [selsortCapN]uint64) {
	s := make([]uint64, n)
	x := seed
	for i := uint64(0); i < n; i++ {
		x = x*6364136223846793005 + 1442695040888963407
		s[i] = x
	}
	var pre [selsortCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	selectionSort(s)
	var post [selsortCapN]uint64
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
