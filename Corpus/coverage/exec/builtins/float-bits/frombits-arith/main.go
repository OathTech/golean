package main

import "math"

// Float64frombits feeds ordinary arithmetic: 2.0 from bits, times three,
// converted; a subnormal from bits compared against zero; bits of a sum.
func frombitsArith() (int, bool, uint64, uint64) {
	two := math.Float64frombits(0x4000000000000000)
	sub := math.Float64frombits(0x0000000000000001)
	half := math.Float64frombits(0x3FE0000000000000)
	return int(two * 3), sub > 0, math.Float64bits(two + half), math.Float64bits(two / 3)
}
