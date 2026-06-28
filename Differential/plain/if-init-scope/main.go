package main

import "fmt"

func main() {
	z := 0
	if v := 3; v > 5 {
		z = v
	} else {
		z = v + 10
	}
	z += 100
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
