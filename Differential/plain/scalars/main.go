package main

import "fmt"

func main() {
	x := 10
	y := 3
	z := x - y

	_, _, _ = x, y, (-7 / 3)
	_ = -7 % 3
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
