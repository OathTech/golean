package main

import "fmt"

func arraySliceAlias() int {
	a := [3]int{1, 2, 3}
	s := a[1:3]
	s[0] = 9
	z := a[1] + len(s)*10 + cap(s)*100

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", arraySliceAlias())
}
