package main

import "fmt"

func main() {
	arr := [3]int{1, 2, 3}
	cp := arr
	cp[0] = 99

	sl := []int{1, 2, 3}
	alias := sl
	alias[0] = 99

	z := arr[0]*100000 + cp[0]*1000 + sl[0]*10 + alias[0]
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
