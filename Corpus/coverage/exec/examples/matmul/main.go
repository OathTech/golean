package main

import "fmt"

// matN: the fixed matrix dimension. Matrices are [matN][matN]uint64
// throughout — Go arrays are VALUES (copied on call and return), which
// is exactly why matrix multiply fits the pass-by-value fragment.
const matN = 3

func matMul(a, b [matN][matN]uint64) [matN][matN]uint64 {
	var c [matN][matN]uint64
	for i := 0; i < matN; i++ {
		for j := 0; j < matN; j++ {
			var sum uint64
			for k := 0; k < matN; k++ {
				sum += a[i][k] * b[k][j]
			}
			c[i][j] = sum
		}
	}
	return c
}

// seedMat: the seeded family — m[i][j] = seed + (i*matN + j), wrapping.
func seedMat(seed uint64) [matN][matN]uint64 {
	var m [matN][matN]uint64
	for i := 0; i < matN; i++ {
		for j := 0; j < matN; j++ {
			m[i][j] = seed + uint64(i*matN+j)
		}
	}
	return m
}

// scalarDiag: x times the identity (x on the diagonal, zero elsewhere).
func scalarDiag(x uint64) [matN][matN]uint64 {
	var m [matN][matN]uint64
	for i := 0; i < matN; i++ {
		m[i][i] = x
	}
	return m
}

// mulIdentitySeed: I * seedMat(seed) — identity times anything is the
// thing; the returned matrix is the observable.
func mulIdentitySeed(seed uint64) [matN][matN]uint64 {
	return matMul(scalarDiag(1), seedMat(seed))
}

// mulZeroSeed: 0 * seedMat(seed) — the zero matrix annihilates.
func mulZeroSeed(seed uint64) [matN][matN]uint64 {
	return matMul(scalarDiag(0), seedMat(seed))
}

// mulScalarDiag: (x*I)(y*I), element [1][1] = x*y (wrapping mod 2^64).
func mulScalarDiag(x, y uint64) uint64 {
	c := matMul(scalarDiag(x), scalarDiag(y))
	return c[1][1]
}

// mulSeedTrace: square the seeded matrix and return the trace of the
// square (wrapping mod 2^64).
func mulSeedTrace(seed uint64) uint64 {
	m := seedMat(seed)
	c := matMul(m, m)
	return c[0][0] + c[1][1] + c[2][2]
}

// matmul_harness_r: the S3 RELATIONAL harness. Builds
// a[i][j] = seed + (i*matN + j) and b[i][j] = (i*matN + j) + 1, runs the
// subject, and returns (a, b, product) so the Lean postcondition relates
// the returned matrices directly. Real Go, ghost ladder rung 0.
func matmul_harness_r(seed uint64) ([matN][matN]uint64, [matN][matN]uint64, [matN][matN]uint64) {
	a := seedMat(seed)
	b := seedMat(1)
	return a, b, matMul(a, b)
}

func main() {
	c := matMul(seedMat(1), scalarDiag(2))
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", c[2][2])
}
