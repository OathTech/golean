package main

import "fmt"

func gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// gcd_harness: three-phase shape; setup and test are identities
// (argument-input subject, returned data is the observable).
func gcd_harness(a, b uint64) uint64 {
	r := gcd(a, b)
	return r
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", gcd(12, 18))
}
