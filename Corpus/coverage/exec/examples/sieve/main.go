package main

import "fmt"

// countPrimes: sieve of Eratosthenes, bounded. Allocates a []bool
// composite table up to n and counts the primes <= n.
// BOUNDEDNESS: every corpus row is a real run of the fuel-bounded
// machine, so n stays SMALL — no corpus row above n = 60.
func countPrimes(n uint64) uint64 {
	if n < 2 {
		return 0
	}
	composite := make([]bool, n+1)
	for i := uint64(2); i*i <= n; i++ {
		if !composite[i] {
			for j := i * i; j <= n; j += i {
				composite[j] = true
			}
		}
	}
	count := uint64(0)
	for i := uint64(2); i <= n; i++ {
		if !composite[i] {
			count++
		}
	}
	return count
}

// isPrimeSieved: 1 if q <= n and q is prime under the sieve up to n,
// else 0 (q > n is out of the sieve's range, answered 0). Same
// boundedness note as countPrimes: keep n small in every row.
func isPrimeSieved(n, q uint64) uint64 {
	if q > n {
		return 0
	}
	if q < 2 {
		return 0
	}
	composite := make([]bool, n+1)
	for i := uint64(2); i*i <= n; i++ {
		if !composite[i] {
			for j := i * i; j <= n; j += i {
				composite[j] = true
			}
		}
	}
	if composite[q] {
		return 0
	}
	return 1
}

// sieve_harness: S2 scalar three-phase shape; setup and test are
// identities (argument-input subject, returned scalar is the
// observable).
func sieve_harness(n uint64) uint64 {
	return countPrimes(n)
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", countPrimes(30))
}
