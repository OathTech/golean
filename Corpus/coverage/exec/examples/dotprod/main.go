package main

import "fmt"

// dotProduct: the accumulate loop acc += a[i]*b[i], wrapping mod 2^64.
// Mismatched lengths are guarded by walking min(len(a), len(b)),
// written explicitly (no stdlib call).
func dotProduct(a, b []uint64) uint64 {
	n := len(a)
	if len(b) < n {
		n = len(b)
	}
	acc := uint64(0)
	for i := 0; i < n; i++ {
		acc += a[i] * b[i]
	}
	return acc
}

func dotFour(a1, a2, b1, b2 uint64) uint64 {
	a := []uint64{a1, a2}
	b := []uint64{b1, b2}
	return dotProduct(a, b)
}

func dotOne(a, b uint64) uint64 {
	av := []uint64{a}
	bv := []uint64{b}
	return dotProduct(av, bv)
}

func dotEmpty() uint64 {
	av := []uint64{}
	bv := []uint64{}
	return dotProduct(av, bv)
}

// dotUneven: mismatched lengths (3 vs 2) so the explicit min guard is
// exercised on a non-trivial path — a3 must not contribute.
func dotUneven(a1, a2, a3, b1, b2 uint64) uint64 {
	av := []uint64{a1, a2, a3}
	bv := []uint64{b1, b2}
	return dotProduct(av, bv)
}

// dotCapN: the fixed observation cap of the S3 relational harness.
const dotCapN = 8

// dotprod_harness_r: S3 RELATIONAL harness. Setup builds the families
// a[i] = seed + i and b[i] = i + 1; two copy loops lift them into the
// fixed-cap arrays av and bv (the pass-by-value fragment's
// unbounded-data workaround, zero-padded past n); the observable is
// (av, bv, dot) so the Lean postcondition can relate the returned data
// directly. Real Go, ghost ladder rung 0; harness bound n <= 8.
func dotprod_harness_r(n, seed uint64) ([dotCapN]uint64, [dotCapN]uint64, uint64) {
	a := make([]uint64, n)
	b := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		a[i] = seed + i
		b[i] = i + 1
	}
	var av [dotCapN]uint64
	for i := uint64(0); i < n; i++ {
		av[i] = a[i]
	}
	var bv [dotCapN]uint64
	for i := uint64(0); i < n; i++ {
		bv[i] = b[i]
	}
	dot := dotProduct(a, b)
	return av, bv, dot
}

func main() {
	d := dotFour(2, 3, 4, 5)
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", d)
}
