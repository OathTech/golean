package main

import "fmt"

func main() {
	defer func() {
		if recover() != nil {
			fmt.Println("{\"message\":\"makeslice: cap out of range\",\"status\":\"panic\"}")
		}
	}()

	length := 5
	capacity := 3
	s := make([]int, length, capacity)
	_ = len(s)
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
