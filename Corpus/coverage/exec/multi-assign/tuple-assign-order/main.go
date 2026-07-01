package main

import "fmt"

func tupleAssignOrder() int {
	a := []int{0, 0, 0}
	i := 0
	i, a[i] = 1, 2
	z := i*1000 + a[0]*100 + a[1]*10 + a[2]

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", tupleAssignOrder())
}
