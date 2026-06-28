package main

import "fmt"

type cell struct {
	v int
}

func main() {
	var z int
	p := new(cell)
	z = z + p.v
	p.v = 9
	z = z + p.v*10

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
