package main

import "fmt"

func main() {
	var z int
	var s []int
	if s == nil {
		z = z + 1
	}
	if len(s) == 0 {
		z = z + 10
	}
	if cap(s) == 0 {
		z = z + 100
	}
	t := make([]int, 0)
	if t == nil {
		z = z + 1000
	} else {
		z = z + 2000
	}
	u := []int{}
	if u == nil {
		z = z + 10000
	} else {
		z = z + 20000
	}
	v := append(s)
	if v == nil {
		z = z + 100000
	}

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
