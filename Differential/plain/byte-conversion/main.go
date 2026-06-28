package main

import "fmt"

func main() {
	var big int32
	big = 300
	z := byte(big)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
