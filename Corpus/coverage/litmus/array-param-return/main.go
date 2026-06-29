package main

import "fmt"

func bumpArray(a [2]int) [2]int {
	b := a
	b[0] = b[0] + 1
	return b
}

func main() {
	a := [2]int{4, 5}
	b := bumpArray(a)
	z := b[0] + b[1]
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
