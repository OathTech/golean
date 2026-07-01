package main

import "fmt"

func stringByteLen() int {
	s := "héllo"
	z := len(s)
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", stringByteLen())
}
