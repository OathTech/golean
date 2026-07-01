package main

import "fmt"

func foo() int {
	x, y, z := 1, 2, 3
	y, z, x = z, x, y
	return x*100 + y*10 + z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", foo())
}
