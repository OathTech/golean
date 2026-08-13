package main

import "fmt"

func minMax(s []uint64) (uint64, uint64) {
	lo, hi := s[0], s[0]
	for i := 1; i < len(s); i++ {
		if s[i] < lo {
			lo = s[i]
		}
		if s[i] > hi {
			hi = s[i]
		}
	}
	return lo, hi
}

func minMaxFour(a, b, c, d uint64) (uint64, uint64) {
	s := []uint64{a, b, c, d}
	return minMax(s)
}

func minMaxThree(a, b, c uint64) (uint64, uint64) {
	s := []uint64{a, b, c}
	return minMax(s)
}

func minMaxOne(a uint64) (uint64, uint64) {
	s := []uint64{a}
	return minMax(s)
}

func minMaxEmpty() (uint64, uint64) {
	s := []uint64{}
	return minMax(s)
}

func main() {
	lo, hi := minMaxFour(3, 1, 4, 1)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		lo, hi,
	)
}
