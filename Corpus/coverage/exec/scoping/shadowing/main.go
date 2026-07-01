package main

import "fmt"

func shadowing() int {
	err := "outer"
	if true {
		err := "inner"
		_ = err
	}
	z := len(err)
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", shadowing())
}
