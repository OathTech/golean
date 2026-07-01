package main

import "fmt"

func copyNil() int {
	var s []int
	dst := []int{7, 8}
	n1 := copy(dst, s)
	n2 := copy(s, dst)
	z := n1*1000 + n2*100 + dst[0]*10 + dst[1]

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", copyNil())
}
