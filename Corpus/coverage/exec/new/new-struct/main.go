package main

import "fmt"

type cell struct {
	v int
}

func newStruct() int {
	var z int
	p := new(cell)
	z = z + p.v
	p.v = 9
	z = z + p.v*10

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", newStruct())
}
