package main

import "fmt"

func main() {
	v := 42
	ar, br := &v, &v
	arr, brr := &ar, &br

	if ar != br {
		fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
		return
	}
	if arr != brr {
		fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
		return
	}
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
