package main

import "fmt"

func mapNilEq() int {
	var z int
	var m map[int]int
	if m == nil {
		z = z + 1
	}
	v, ok := m[4]
	z = z + v*10
	if ok {
		z = z + 100
	} else {
		z = z + 1000
	}
	m = make(map[int]int)
	if m != nil {
		z = z + 10000
	}

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", mapNilEq())
}
