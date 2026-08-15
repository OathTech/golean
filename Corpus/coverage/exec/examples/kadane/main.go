package main

import "fmt"

// kadane: maximum-subarray sum via the running-best scan. The empty
// slice is defined explicitly (0) so the s[0] read below is guarded.
// All-negative input returns the largest single element, never 0.
func kadane(s []int64) int64 {
	if len(s) == 0 {
		return 0
	}
	best := s[0]
	cur := s[0]
	for i := 1; i < len(s); i++ {
		if cur < 0 {
			cur = s[i]
		} else {
			cur = cur + s[i]
		}
		if cur > best {
			best = cur
		}
	}
	return best
}

func kadaneFour(a, b, c, d int64) int64 {
	s := []int64{a, b, c, d}
	return kadane(s)
}

func kadaneThree(a, b, c int64) int64 {
	s := []int64{a, b, c}
	return kadane(s)
}

func kadaneOne(a int64) int64 {
	s := []int64{a}
	return kadane(s)
}

func kadaneEmpty() int64 {
	s := []int64{}
	return kadane(s)
}

// kadaneCapN: the fixed observation cap of the S3 relational harness.
const kadaneCapN = 8

// kadane_harness_r: S3 RELATIONAL harness. Setup builds the
// alternating-sign family s[i] = seed + i with every odd index
// negated, copies it into the fixed-cap pre-state array, runs the
// subject, and returns (pre, best) so a postcondition can relate the
// returned data directly. Real Go, ghost ladder rung 0; bound n <= 8.
func kadane_harness_r(n, seed int64) ([kadaneCapN]int64, int64) {
	s := make([]int64, n)
	for i := int64(0); i < n; i++ {
		s[i] = seed + i
		if i%2 == 1 {
			s[i] = -s[i]
		}
	}
	var pre [kadaneCapN]int64
	for i := int64(0); i < n; i++ {
		pre[i] = s[i]
	}
	best := kadane(s)
	return pre, best
}

func main() {
	x := kadaneFour(4, -1, 2, -7)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", x)
}
