package main

import "fmt"

func test() {
	v := 42
	ar, br := &v, &v
	arr, brr := &ar, &br

	_, _ = ar == br, arr == brr
}

func main() {
	test()
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
