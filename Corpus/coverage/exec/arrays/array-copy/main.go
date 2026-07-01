package main

import "fmt"

func arrayCopy() int {
	a := [2]int{1, 2}
	b := a
	b[0] = 9
	z := a[0] + b[0]

	_ = a
	_ = b
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", arrayCopy())
}
