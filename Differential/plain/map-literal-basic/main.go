package main

import "fmt"

func main() {
	m := map[int]int{1: 10, 2: 20}
	z := len(m)*100 + m[1] + m[2]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
