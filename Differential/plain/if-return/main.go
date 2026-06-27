package main

import "fmt"

func ifReturn(x int) int {
	z := 100
	if x > 0 {
		z = x
		return z
	} else {
		z = 0 - x
	}
	z = z + 100
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", ifReturn(7))
}
