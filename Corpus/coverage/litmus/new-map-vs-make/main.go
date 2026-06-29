package main

import "fmt"

func main() {
	z := 0
	p := new(map[string]int)
	if *p == nil {
		z += 1
	}
	m := make(map[string]int)
	if m != nil {
		z += 10
	}
	m["k"] = 7
	z += m["k"] * 100
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
