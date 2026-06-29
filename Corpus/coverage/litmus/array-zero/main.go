package main

import "fmt"

func main() {
	var a [2]int
	z := a[0] + a[1]
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
