package main

import "fmt"

func mapLiteralBool() int {
	var z int
	m := map[bool]bool{true: true, false: false}
	if m[true] {
		z = z + 1
	}
	if m[false] {
		z = z + 10
	} else {
		z = z + 100
	}
	z = z + len(m)*1000

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", mapLiteralBool())
}
