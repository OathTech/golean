package main

import "fmt"

func main() {
	s := []int{1, 2, 3}
	s[1] = 7
	z := s[0] + s[1] + s[2] + len(s)*10 + cap(s)*100

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
