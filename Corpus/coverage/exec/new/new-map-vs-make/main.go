package main

import "fmt"

func newMapVsMake() int {
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
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", newMapVsMake())
}
