package main

import "fmt"

func test(x, y int) int {
	z := 0
	for i := 0; i < x; i += 1 {
		z += y
	}
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", test(6, 7))
}
