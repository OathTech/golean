package main

import "fmt"

func copyMin() int {
	dst := make([]int, 2)
	src := []int{1, 2, 3, 4}
	n := copy(dst, src)
	var nilSlice []int
	z := n*1000 + dst[0]*100 + dst[1]*10 + copy(nilSlice, src)
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", copyMin())
}
