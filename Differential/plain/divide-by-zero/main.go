package main

import "fmt"

func main() {
	defer func() {
		if recover() != nil {
			fmt.Println("{\"message\":\"GoCore panic: integer divide by zero\",\"status\":\"panic\"}")
		}
	}()

	y := 0
	_ = 1 / y
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
