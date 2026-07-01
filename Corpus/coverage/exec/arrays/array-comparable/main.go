package main

import "fmt"

func arrayComparable() int {
	a := [3]int{1, 2, 3}
	b := [3]int{1, 2, 3}
	c := [3]int{1, 2, 4}
	z := 0
	if a == b {
		z += 1
	}
	if a != c {
		z += 20
	}
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", arrayComparable())
}
