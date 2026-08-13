package main

import "fmt"

func insertionSort(s []uint64) {
	for i := 1; i < len(s); i++ {
		for j := i; j > 0 && s[j-1] > s[j]; j-- {
			s[j-1], s[j] = s[j], s[j-1]
		}
	}
}

func sortFour(a, b, c, d uint64) (uint64, uint64, uint64, uint64) {
	s := []uint64{a, b, c, d}
	insertionSort(s)
	return s[0], s[1], s[2], s[3]
}

func sortThree(a, b, c uint64) (uint64, uint64, uint64) {
	s := []uint64{a, b, c}
	insertionSort(s)
	return s[0], s[1], s[2]
}

func sortOne(a uint64) uint64 {
	s := []uint64{a}
	insertionSort(s)
	return s[0]
}

func sortEmpty() int {
	s := []uint64{}
	insertionSort(s)
	return len(s)
}

// isort_harness: three-phase harness — setup builds the wrapped
// multiplicative family s[i] = seed * (i+1); test verifies IN GO
// (inside the verified footprint) that the result is sorted AND a
// permutation of the rebuilt input family (count-based), folding
// into a verdict.
func isort_harness(n, seed uint64) uint64 {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed * (i + 1)
	}
	insertionSort(s)
	ok := uint64(1)
	for i := uint64(1); i < n; i++ {
		if s[i-1] > s[i] {
			ok = 0
		}
	}
	t := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		t[i] = seed * (i + 1)
	}
	for i := uint64(0); i < n; i++ {
		cs := uint64(0)
		ct := uint64(0)
		for j := uint64(0); j < n; j++ {
			if s[j] == t[i] {
				cs++
			}
			if t[j] == t[i] {
				ct++
			}
		}
		if cs != ct {
			ok = 0
		}
	}
	return ok
}

func main() {
	a, b, c, d := sortFour(4, 2, 3, 1)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a, b, c, d,
	)
}
