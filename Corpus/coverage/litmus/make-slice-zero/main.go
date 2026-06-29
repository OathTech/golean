package main

import "fmt"

func main() {
	var z int
	s := make([]int, 0)
	t := make([]int, 0, 3)
	u := append(t, 6, 7)
	if s == nil {
		z = z + 1
	} else {
		z = z + 2
	}
	z = z*100000 + len(s)*10000 + cap(s)*1000 + len(u)*100 + cap(u)*10 + u[1]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
