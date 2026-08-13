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

func main() {
	a, b, c, d := sortFour(4, 2, 3, 1)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a, b, c, d,
	)
}
