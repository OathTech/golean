package main

// spec#Min_and_max block Min_and_max-3-fea8bda1: the floating-point
// special-case table for min/max:
//   min(-0.0, 0.0) == -0.0, max(-0.0, 0.0) == 0.0
//     ("negative zero is smaller than (non-negative) zero")
//   min(-Inf, y) == -Inf, max(-Inf, y) == y
//   min(+Inf, y) == y,    max(+Inf, y) == +Inf
//   min(NaN, y) == NaN,   max(NaN, y) == NaN
//     ("if any argument is a NaN, the result is a NaN")
// The spec asserts NaN-ness of the result, not a payload, so the NaN
// observable is r != r. Zero signs are observed through 1/r (-Inf for
// -0.0, +Inf for +0.0). Negative zero must be produced at run time
// (-z of a zero VARIABLE): the spec's Representability section says
// constants never result in an IEEE negative zero. Inf and NaN come
// from runtime float division (corpus convention, cf.
// floats/division-specials). Expected: every returned bool is true,
// and the y-propagating results equal y == 12.5.

func minMaxSignedZero() (bool, bool, bool, bool) {
	z := 0.0
	neg := -z // runtime negative zero
	lo := min(neg, z)
	hi := max(neg, z)
	return lo == 0, 1/lo < 0, hi == 0, 1/hi > 0
}

func minMaxInfinities() (bool, float64, float64, bool) {
	z := 0.0
	posInf := 1.0 / z
	negInf := -1.0 / z
	y := 12.5
	return min(negInf, y) == negInf, max(negInf, y),
		min(posInf, y), max(posInf, y) == posInf
}

func minMaxNaN() (bool, bool, bool) {
	z := 0.0
	nan := z / z
	y := 12.5
	lo := min(nan, y)
	hi := max(nan, y)
	return lo != lo, hi != hi, min(y, nan) != min(y, nan)
}

func main() {
	minMaxSignedZero()
}
