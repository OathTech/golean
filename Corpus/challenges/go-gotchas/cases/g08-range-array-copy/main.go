package main

import "fmt"

func main() {
	arr := [3]int{1, 2, 3}
	for _, v := range arr {
		v *= 10
		_ = v
	}
	sl := []int{1, 2, 3}
	for i := range sl {
		sl[i] *= 10
	}
	z := arr[0]*100000 + arr[1]*10000 + arr[2]*1000 + sl[0]*100 + sl[1]*10 + sl[2]
	fmt.Printf("{\"case\":\"g08-range-array-copy\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
