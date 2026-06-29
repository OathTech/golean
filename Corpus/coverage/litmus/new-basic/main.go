package main

import "fmt"

func main() {
	var z int
	p := new(int)
	z = z + *p
	*p = 7
	z = z + *p*10
	a := new([2]int)
	(*a)[1] = 3
	z = z + (*a)[1]*100

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
