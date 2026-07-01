package main

import "fmt"

func test() int {
	v := 42
	ar, br := &v, &v
	arr, brr := &ar, &br

	score := 0
	if ar == br {
		score += 1
	}
	if arr == brr {
		score += 10
	}
	return score
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", test())
}
