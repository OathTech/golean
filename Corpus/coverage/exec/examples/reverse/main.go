package main

import "fmt"

func reverse(s []uint64) {
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		s[i], s[j] = s[j], s[i]
	}
}

func reverseFour(a, b, c, d uint64) (uint64, uint64, uint64, uint64) {
	s := []uint64{a, b, c, d}
	reverse(s)
	return s[0], s[1], s[2], s[3]
}

func reverseThree(a, b, c uint64) (uint64, uint64, uint64) {
	s := []uint64{a, b, c}
	reverse(s)
	return s[0], s[1], s[2]
}

func reverseOne(a uint64) uint64 {
	s := []uint64{a}
	reverse(s)
	return s[0]
}

func reverseEmpty() int {
	s := []uint64{}
	reverse(s)
	return len(s)
}

// reverse_harness: three-phase harness (harness ruling 2026-08-13).
// setup_reverse_state: build s from the scalar parameters — the
// input FAMILY s[i] = seed + i (wrapping); test_reverse_state:
// verify the reversal element-wise in Go and fold into a verdict.
func reverse_harness(n, seed uint64) uint64 {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	reverse(s)
	ok := uint64(1)
	for i := uint64(0); i < n; i++ {
		if s[i] != seed+(n-1-i) {
			ok = 0
		}
	}
	return ok
}

func main() {
	a, b, c, d := reverseFour(1, 2, 3, 4)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a, b, c, d,
	)
}
