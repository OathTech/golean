package main

import "fmt"

func setMembership() int {
	s := map[uint64]struct{}{}
	s[3] = struct{}{}
	s[7] = struct{}{}
	_, in3 := s[3]
	_, in5 := s[5]
	r := len(s) * 100
	if in3 {
		r += 10
	}
	if in5 {
		r += 1
	}
	return r
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", setMembership())
}
