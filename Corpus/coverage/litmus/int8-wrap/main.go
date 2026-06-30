package main

import "fmt"

func int8Wrap() int8 {
	var x int8
	x = 127
	x = x + 1
	z := x
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", int8Wrap())
}
