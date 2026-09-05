package main

import "math"

// Bits of constants and runtime values: 1.0, -2.5, 0.1 (the classic
// round-to-nearest pattern 0x3FB999999999999A), 1e300, the RUNTIME
// negative zero (a `-0.0` LITERAL folds to +0 — spec constant arithmetic),
// and an overflow to +Inf computed at run time.
func literalsAndZero() (uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	z := 0.0
	nz := -z
	big := 1e308
	inf := big * 10
	return math.Float64bits(1.0), math.Float64bits(-2.5), math.Float64bits(0.1),
		math.Float64bits(1e300), math.Float64bits(nz), math.Float64bits(-0.0), math.Float64bits(inf)
}
