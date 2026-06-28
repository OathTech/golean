package main

import "fmt"

func main() {
	var z int
	var empty string
	s := "hi"
	t := s + "!"
	z = len(empty)*100 + len(s)*10 + len(t)
	if empty == "" {
		z = z + 1000
	}
	if t == "hi!" {
		z = z + 10000
	}

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
