package main

import "fmt"

func main() {
	a := [3]int{1, 2, 3}
	s := a[1:3]
	s[0] = 9
	z := a[1] + len(s)*10 + cap(s)*100

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
