package main

import "fmt"

func sum(xs ...int) int {
	t := 0
	for _, x := range xs {
		t += x
	}
	return t
}

func main() {
	var none []int
	parts := []int{4, 5}
	merged := append([]int{1, 2, 3}, parts...)
	z := sum(none...)*1000 + sum(1, 2, 3)*100 + len(merged)*10 + merged[4]
	fmt.Printf("{\"case\":\"g24-variadic\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
