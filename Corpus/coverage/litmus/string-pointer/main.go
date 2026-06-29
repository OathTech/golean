package main

import "fmt"

func main() {
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

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
