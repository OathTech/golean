package main

import "fmt"

func main() {
	a := []int{0, 0, 0}
	i := 0
	i, a[i] = 1, 2
	z := i*1000 + a[0]*100 + a[1]*10 + a[2]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
