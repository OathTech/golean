package main

import "fmt"

func stringPointer() int {
	var z int
	s := "test"
	p := &s
	if *p == "test" {
		z = z + 1
	}
	*p = "go"
	if s == "go" {
		z = z + 10
	}
	z = z + len(*p)*100

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", stringPointer())
}
