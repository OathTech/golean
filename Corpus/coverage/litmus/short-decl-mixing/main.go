package main

import "fmt"

func main() {
	a := 1
	a, b := 2, 3
	z := a*10 + b
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
