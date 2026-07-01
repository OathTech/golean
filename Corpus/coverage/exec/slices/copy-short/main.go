package main

import "fmt"

func copyShort() int {
	dst := []int{9, 8}
	src := []int{1, 2, 3, 4}
	n := copy(dst, src)
	z := n*100 + dst[0]*10 + dst[1]

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", copyShort())
}
