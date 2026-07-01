package main

import "fmt"

func scalars() int {
	x := 10
	y := 3
	z := x - y

	_, _, _ = x, y, (-7 / 3)
	_ = -7 % 3
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", scalars())
}
