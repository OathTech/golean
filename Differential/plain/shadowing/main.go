package main

import "fmt"

func main() {
	err := "outer"
	if true {
		err := "inner"
		_ = err
	}
	z := len(err)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
