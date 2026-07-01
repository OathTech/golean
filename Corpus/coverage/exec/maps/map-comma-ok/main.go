package main

import "fmt"

func mapCommaOk() int {
	m := make(map[int]int)
	v1, ok1 := m[3]
	m[3] = 10
	v2, ok2 := m[3]
	z := v1 + v2*10
	if ok1 {
		z = z + 1000
	} else {
		z = z + 100
	}
	if ok2 {
		z = z + 2000
	} else {
		z = z + 200
	}

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", mapCommaOk())
}
