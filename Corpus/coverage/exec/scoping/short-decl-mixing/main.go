package main

import "fmt"

func shortDeclMixing() int {
	a := 1
	a, b := 2, 3
	z := a*10 + b
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", shortDeclMixing())
}
