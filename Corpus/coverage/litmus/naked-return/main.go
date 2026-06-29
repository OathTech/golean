package main

import "fmt"

func split(sum int) (a int, b int) {
	a = sum * 4 / 9
	b = sum - a
	return
}

func main() {
	a, b := split(17)
	z := a*10 + b
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
