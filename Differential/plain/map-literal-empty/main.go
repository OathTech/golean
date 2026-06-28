package main

import "fmt"

func main() {
	var z int
	m := map[int]int{}
	if m == nil {
		z = z + 1
	} else {
		z = z + 10
	}
	z = z + len(m)*100

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
