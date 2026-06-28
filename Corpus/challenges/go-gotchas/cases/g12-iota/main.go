package main

import "fmt"

const (
	_  = iota
	KB = 1 << (10 * iota)
	MB
	GB
)

func main() {
	z := KB + MB + GB
	fmt.Printf("{\"case\":\"g12-iota\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
