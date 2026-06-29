package main

import "fmt"

func main() {
	var s []int
	dst := []int{7, 8}
	n1 := copy(dst, s)
	n2 := copy(s, dst)
	z := n1*1000 + n2*100 + dst[0]*10 + dst[1]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
