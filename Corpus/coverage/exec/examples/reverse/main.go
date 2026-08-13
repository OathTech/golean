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

func main() {
	a, b, c, d := reverseFour(1, 2, 3, 4)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a, b, c, d,
	)
}
