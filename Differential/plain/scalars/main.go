package main

import "fmt"

func main() {
	x := 10
	y := 3
	z := x - y

	if z != y &&
		(z > 0 || z == 0) &&
		!(z < 0) &&
		(-7/3) == -2 &&
		(-7%3) == -1 {
		fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
		return
	}

	fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
}
