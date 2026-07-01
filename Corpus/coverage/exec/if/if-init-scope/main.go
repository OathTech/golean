package main

import "fmt"

func ifInitScope() int {
	z := 0
	if v := 3; v > 5 {
		z = v
	} else {
		z = v + 10
	}
	z += 100
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", ifInitScope())
}
