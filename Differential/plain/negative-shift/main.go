package main

import "fmt"

func main() {
	defer func() {
		if recover() != nil {
			fmt.Println("{\"message\":\"negative shift count\",\"status\":\"panic\"}")
		}
	}()

	s := 0 - 1
	_ = 1 << s
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
