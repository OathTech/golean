package main

import "math"

// A NaN built from bits BEHAVES as a NaN (n != n, every ordering false)
// and its payload survives the identity round-trip and negation (fneg is
// a sign-bit flip on both sides — gc XORPS, the machine `fneg64`).
func nanSemantics() (bool, bool, bool, uint64, uint64) {
	n := math.Float64frombits(0x7FF8000000000001)
	neg := -n
	return n != n, n < 1, n > 1, math.Float64bits(n), math.Float64bits(neg)
}
