package main

import "fmt"

func main() {
	a := [2]int{1, 2}
	b := a
	b[0] = 9
	z := a[0] + b[0]

	_ = a
	_ = b
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
