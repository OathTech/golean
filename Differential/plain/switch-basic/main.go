package main

import "fmt"

func classify(n int) int {
	switch n {
	case 1:
		return 10
	case 2, 3:
		return 20
	default:
		return 30
	}
}

func exprless(n int) int {
	switch {
	case n < 0:
		return 1
	case n == 0:
		return 2
	default:
		return 3
	}
}

func main() {
	z := classify(1) + classify(3) + classify(9) + exprless(-1) + exprless(0) + exprless(5)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
