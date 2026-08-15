package main

import "fmt"

// twoSum: the O(n^2) double loop. Returns the FIRST index pair (i, j)
// in scan order with i < j and s[i]+s[j] == target (wrapping uint64
// addition). When no pair exists it returns
// (uint64(len(s)), uint64(len(s))) — an out-of-range sentinel.
func twoSum(s []uint64, target uint64) (uint64, uint64) {
	n := uint64(len(s))
	for i := uint64(0); i < n; i++ {
		for j := i + 1; j < n; j++ {
			if s[i]+s[j] == target {
				return i, j
			}
		}
	}
	return n, n
}

func twoSumFour(a, b, c, d, target uint64) (uint64, uint64) {
	s := []uint64{a, b, c, d}
	return twoSum(s, target)
}

func twoSumOne(a, target uint64) (uint64, uint64) {
	s := []uint64{a}
	return twoSum(s, target)
}

func twoSumEmpty(target uint64) (uint64, uint64) {
	s := []uint64{}
	return twoSum(s, target)
}

// twosumCapN: the fixed observation cap of the S3 relational harness.
// The returned array is `[twosumCapN]uint64`, so the harness's own
// bound is `n <= 8` — plainly visible in the source.
const twosumCapN = 8

// twosum_harness_r: the S3 RELATIONAL harness. Setup builds the family
// s[i] = seed + i (wrapping uint64 addition); a copy loop lifts the
// pre-state into a fixed-cap array (the pass-by-value fragment's
// unbounded-data workaround); then the subject runs. Returning
// (vals, i, j) lets the postcondition relate the returned data
// directly: either i < j < n with vals[i]+vals[j] = target and (i, j)
// first in scan order, or i = j = n (the not-found sentinel).
// Real Go, ghost ladder rung 0.
func twosum_harness_r(n, seed, target uint64) ([twosumCapN]uint64, uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	var vals [twosumCapN]uint64
	for i := uint64(0); i < n; i++ {
		vals[i] = s[i]
	}
	i, j := twoSum(s, target)
	return vals, i, j
}

func main() {
	i, j := twoSumFour(2, 7, 11, 15, 9)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		i, j,
	)
}
