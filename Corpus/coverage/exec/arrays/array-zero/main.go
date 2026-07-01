package main

import "fmt"

func arrayZero() int {
	var a [2]int
	z := a[0] + a[1]
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", arrayZero())
}
