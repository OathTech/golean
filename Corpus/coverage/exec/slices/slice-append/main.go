package main

import "fmt"

func sliceAppend() int {
	s := make([]int, 2, 4)
	s[0] = 1
	s[1] = 2
	t := append(s, 3, 4)
	t[0] = 7
	u := append(t, 5)
	t[1] = 8
	z := len(t)*100000 + cap(t)*10000 + len(u)*1000 + u[0]*100 + u[1]*10 + u[4]

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", sliceAppend())
}
