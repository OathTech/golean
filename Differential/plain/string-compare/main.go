package main

import "fmt"

func main() {
	var z int
	a := "alpha"
	b := "beta"
	if a < b {
		z = z + 1
	}
	if b > a {
		z = z + 10
	}
	if a <= "alpha" {
		z = z + 100
	}
	if b >= "beta" {
		z = z + 1000
	}

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
