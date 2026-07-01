package main

import "fmt"

func mapBoolValues() int {
	var z int
	m := make(map[int]bool)
	a := m[1]
	m[1] = true
	b := m[1]
	if a {
		z = z + 1
	} else {
		z = z + 10
	}
	if b {
		z = z + 100
	} else {
		z = z + 1000
	}

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", mapBoolValues())
}
