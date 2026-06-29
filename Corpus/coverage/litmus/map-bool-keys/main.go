package main

import "fmt"

func main() {
	m := make(map[bool]int)
	m[true] = 5
	m[false] = 2
	z := len(m)*100 + m[true]*10 + m[false]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
