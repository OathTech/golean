package main

import "fmt"

func sliceLiteral() int {
	s := []int{1, 2, 3}
	s[1] = 7
	z := s[0] + s[1] + s[2] + len(s)*10 + cap(s)*100

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", sliceLiteral())
}
