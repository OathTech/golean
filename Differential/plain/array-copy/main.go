package main

import "fmt"

func main() {
	a := [2]int{1, 2}
	b := a
	b[0] = 9
	z := a[0] + b[0]

	if a == [2]int{1, 2} && b == [2]int{9, 2} {
		fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
		return
	}

	fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
}
