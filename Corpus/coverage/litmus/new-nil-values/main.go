package main

import "fmt"

func newNilValues() int {
	var z int
	s := new([]int)
	if *s == nil {
		z = z + 1
	}
	m := new(map[int]int)
	if *m == nil {
		z = z + 10
	}

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", newNilValues())
}
