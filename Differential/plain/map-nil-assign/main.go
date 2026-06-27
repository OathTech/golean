package main

import "fmt"

func main() {
	defer func() {
		if recover() != nil {
			fmt.Println("{\"message\":\"assignment to entry in nil map\",\"status\":\"panic\"}")
		}
	}()

	var m map[int]int
	m[1] = 2
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
