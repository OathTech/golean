package main

import "fmt"

func stringId(s string) string {
	return s
}

func main() {
	var z int
	s := stringId("go")
	if s == "go" {
		z = z + 1
	}
	z = z + len(s)*10

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
