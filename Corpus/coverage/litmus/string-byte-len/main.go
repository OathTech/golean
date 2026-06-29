package main

import "fmt"

func main() {
	s := "héllo"
	z := len(s)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
