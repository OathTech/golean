package main

import "fmt"

func search(s []uint64, target uint64) int {
	lo, hi := 0, len(s)
	for lo < hi {
		mid := (lo + hi) / 2
		if s[mid] < target {
			lo = mid + 1
		} else {
			hi = mid
		}
	}
	if lo < len(s) && s[lo] == target {
		return lo
	}
	return -1
}

func searchFour(a, b, c, d, target uint64) int {
	s := []uint64{a, b, c, d}
	return search(s, target)
}

func searchOne(a, target uint64) int {
	s := []uint64{a}
	return search(s, target)
}

func searchEmpty(target uint64) int {
	s := []uint64{}
	return search(s, target)
}

// search_harness: three-phase harness — setup builds the sorted
// family s[i] = seed + 2*i (precondition: no wrap, so it IS sorted
// with gaps); the target is a raw parameter, covering found and
// not-found; returned index is the observable.
func search_harness(n, seed, t uint64) int {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + 2*i
	}
	return search(s, t)
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", searchFour(2, 3, 5, 8, 5))
}
