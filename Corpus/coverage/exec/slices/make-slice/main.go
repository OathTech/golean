package main

import "fmt"

func makeSlice() int {
	s := make([]int, 3, 5)
	s[0] = 7
	z := s[0] + len(s)*10 + cap(s)*100

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", makeSlice())
}
