package main

import "fmt"

func main() {
	a := [5]int{1, 2, 3, 4, 5}
	s := a[1:3:4]
	s[1] = 9
	z := len(s)*1000 + cap(s)*100 + a[0]*10 + a[2]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
