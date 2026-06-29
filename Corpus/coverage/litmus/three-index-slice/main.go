package main

import "fmt"

func main() {
	a := []int{1, 2, 3, 4}
	b := a[:2:2]
	b = append(b, 99)
	z := a[0]*1000000 + a[1]*100000 + a[2]*10000 + a[3]*1000 +
		b[0]*100 + b[1]*10 + b[2]
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
