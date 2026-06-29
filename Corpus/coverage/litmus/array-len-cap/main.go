package main

import "fmt"

func main() {
	a := [3]int{1, 2, 3}
	z := len(a) + cap(a)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
