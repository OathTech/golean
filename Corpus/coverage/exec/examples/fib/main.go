package main

import "fmt"

func fib(n uint64) uint64 {
	var a, b uint64 = 0, 1
	for i := uint64(0); i < n; i++ {
		a, b = b, a+b
	}
	return a
}

// fib_harness: the harness ruling's three-phase shape (2026-08-13).
// setup_fib_state: nothing — fib takes no memory input.
// test_fib_state: identity — the result IS the observable.
func fib_harness(n uint64) uint64 {
	r := fib(n)
	return r
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", fib(10))
}
