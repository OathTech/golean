package main

import "fmt"

func main() {
	var x int8
	x = 127
	x = x + 1
	z := x
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
