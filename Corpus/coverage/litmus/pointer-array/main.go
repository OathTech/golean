package main

import "fmt"

func pointerArray() int {
	a := [2]int{4, 5}
	p := &a
	z := p[1]
	p[0] = 9
	z = z + a[0]
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", pointerArray())
}
