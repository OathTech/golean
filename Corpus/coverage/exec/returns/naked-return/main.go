package main

import "fmt"

func split(sum int) (a int, b int) {
	a = sum * 4 / 9
	b = sum - a
	return
}

func nakedReturn() int {
	a, b := split(17)
	z := a*10 + b
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", nakedReturn())
}
