package main

import "fmt"

func byteConversion() byte {
	var big int32
	big = 300
	z := byte(big)
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", byteConversion())
}
