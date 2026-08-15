package main

import "fmt"

func isEven(x uint64) bool {
	return x%2 == 0
}

func steinGCD(a, b uint64) uint64 {
	if a == 0 {
		return b
	}
	if b == 0 {
		return a
	}
	shift := uint64(0)
	for isEven(a) && isEven(b) {
		a /= 2
		b /= 2
		shift++
	}
	for isEven(a) {
		a /= 2
	}
	for {
		for isEven(b) {
			b /= 2
		}
		if a > b {
			a, b = b, a
		}
		b = b - a
		if b == 0 {
			break
		}
	}
	return a << shift
}

// stein_harness: three-phase shape; setup and test are identities
// (argument-input subject, returned data is the observable).
func stein_harness(a, b uint64) uint64 {
	r := steinGCD(a, b)
	return r
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", steinGCD(12, 18))
}
