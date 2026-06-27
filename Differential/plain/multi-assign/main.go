package main

import "fmt"

func main() {
	x, y, z := 1, 2, 3
	y, z, x = z, x, y
	_, _, _ = x, y, z
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
