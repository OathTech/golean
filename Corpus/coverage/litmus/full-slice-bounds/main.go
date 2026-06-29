package main

import "fmt"

func main() {
	defer func() {
		if recover() != nil {
			fmt.Println("{\"message\":\"slice bounds out of range\",\"status\":\"panic\"}")
		}
	}()

	a := [3]int{1, 2, 3}
	m := 4
	s := a[0:2:m]
	_ = len(s)
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
