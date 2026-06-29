package main

import "fmt"

func main() {
	v := 42
	ar, br := &v, &v
	arr, brr := &ar, &br

	_, _ = ar == br, arr == brr
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
