package main

import "fmt"

func main() {
	a := [3]int{1, 2, 3}
	z := a[0] + a[2]
	a[1] = 7
	z = z + a[1]

	if a == [3]int{1, 7, 3} {
		fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
		return
	}

	fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
}
