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

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", searchFour(2, 3, 5, 8, 5))
}
