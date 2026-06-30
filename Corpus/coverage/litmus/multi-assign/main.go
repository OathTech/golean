package main

import "fmt"

func foo() {
	x, y, z := 1, 2, 3
	y, z, x = z, x, y
	_, _, _ = x, y, z
}

func main() {
	foo()
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
