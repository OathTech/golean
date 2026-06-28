package main

import "fmt"

func main() {
	dst := make([]int, 2)
	src := []int{1, 2, 3, 4}
	n := copy(dst, src)
	var nilSlice []int
	z := n*1000 + dst[0]*100 + dst[1]*10 + copy(nilSlice, src)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
