package main

import "fmt"

func main() {
	var z int
	s := new([]int)
	if *s == nil {
		z = z + 1
	}
	m := new(map[int]int)
	if *m == nil {
		z = z + 10
	}

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
