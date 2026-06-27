package main

import "fmt"

func main() {
	s := []int{1, 2, 3, 4}
	dst := s[1:4]
	src := s[0:3]
	n := copy(dst, src)
	z := n*10000 + s[0]*1000 + s[1]*100 + s[2]*10 + s[3]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
