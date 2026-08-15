package main

import "fmt"

// powMod: right-to-left binary exponentiation (exponentiation by
// squaring) modulo mod. Guards: mod == 0 returns 0 by DEFINITION here
// (a plain documented answer, chosen over the Go division panic that
// `% 0` would raise); mod == 1 returns 0 (every residue is 0 mod 1,
// including exp == 0). The multiplies are uint64 and wrap mod 2^64, so
// results are the mathematical base^exp mod m only while
// (mod-1)^2 < 2^64; past that the wrap is part of the pinned behavior.
func powMod(base, exp, mod uint64) uint64 {
	if mod == 0 {
		return 0
	}
	if mod == 1 {
		return 0
	}
	result := uint64(1)
	base = base % mod
	for exp > 0 {
		if exp%2 == 1 {
			result = result * base % mod
		}
		base = base * base % mod
		exp = exp / 2
	}
	return result
}

// powTwo: fixed driver — powers of two modulo the prime 1000000007.
func powTwo(exp uint64) uint64 {
	return powMod(2, exp, 1000000007)
}

// powmod_harness: three-phase shape; setup and test are identities
// (argument-input subject, returned scalar is the observable).
func powmod_harness(base, exp, mod uint64) uint64 {
	r := powMod(base, exp, mod)
	return r
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", powMod(3, 13, 1000000007))
}
