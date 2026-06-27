package main

import "fmt"

func main() {
	defer func() {
		if recover() != nil {
			fmt.Println("{\"message\":\"index out of range\",\"status\":\"panic\"}")
		}
	}()

	a := [2]int{1, 2}
	i := 2
	_ = a[i]
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
