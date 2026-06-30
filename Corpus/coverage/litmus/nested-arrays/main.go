package main

import "fmt"

func nestedArrays() int {
	a := [2][2]int{0: [2]int{1, 2}, 1: [2]int{3, 4}}
	z := a[0][1] + a[1][0]
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", nestedArrays())
}
