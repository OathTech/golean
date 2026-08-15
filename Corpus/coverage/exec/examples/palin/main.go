package main

import "fmt"

func isPalindrome(s []uint64) uint64 {
	i := 0
	j := len(s) - 1
	for i < j {
		if s[i] != s[j] {
			return 0
		}
		i++
		j--
	}
	return 1
}

func palinFour(a, b, c, d uint64) uint64 {
	s := []uint64{a, b, c, d}
	return isPalindrome(s)
}

func palinThree(a, b, c uint64) uint64 {
	s := []uint64{a, b, c}
	return isPalindrome(s)
}

func palinOne(a uint64) uint64 {
	s := []uint64{a}
	return isPalindrome(s)
}

func palinEmpty() uint64 {
	s := []uint64{}
	return isPalindrome(s)
}

// palinCapN: the fixed observation cap of the S3 relational harness.
const palinCapN = 8

// palin_harness_r: the S3 RELATIONAL harness. Setup builds the
// alternating family s[i] = seed + i%2 (go-run verified: verdict 1 for
// n <= 1 and odd n, verdict 0 for even n >= 2); the copy loop lifts the
// pre-state into a fixed-cap array and the subject's verdict rides
// alongside. Real Go, ghost ladder rung 0.
func palin_harness_r(n, seed uint64) ([palinCapN]uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i%2
	}
	var pre [palinCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	v := isPalindrome(s)
	return pre, v
}

func main() {
	x := palinFour(1, 2, 2, 1)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", x)
}
