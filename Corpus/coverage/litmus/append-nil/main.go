package main

import "fmt"

func main() {
	var z int
	var s []int
	t := append(s, 4, 5)
	if s == nil {
		z = z + 1
	}
	z = z + len(t)*100 + t[0]*10 + t[1]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
