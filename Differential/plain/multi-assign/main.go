package main

import "fmt"

func main() {
	x, y, z := 1, 2, 3
	y, z, x = z, x, y
	if x == 2 && y == 3 && z == 1 {
		fmt.Println("{\"status\":\"ok\",\"values\":[]}")
		return
	}
	fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
}
