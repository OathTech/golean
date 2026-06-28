package main

import "fmt"

func sum(xs ...int) int {
	t := 0
	i := 0
	for i < len(xs) {
		t += xs[i]
		i++
	}
	return t
}

func main() {
	var nilSlice []int
	parts := []int{4, 5}
	merged := append([]int{1, 2, 3}, parts...)
	z := sum(nilSlice...)*1000 + sum(1, 2, 3)*100 + len(merged)*10 + merged[4]
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
