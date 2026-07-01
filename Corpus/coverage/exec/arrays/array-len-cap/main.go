package main

import "fmt"

func arrayLenCap() int {
	a := [3]int{1, 2, 3}
	z := len(a) + cap(a)
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", arrayLenCap())
}
