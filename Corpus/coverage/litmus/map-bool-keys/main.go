package main

import "fmt"

func mapBoolKeys() int {
	m := make(map[bool]int)
	m[true] = 5
	m[false] = 2
	z := len(m)*100 + m[true]*10 + m[false]

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", mapBoolKeys())
}
