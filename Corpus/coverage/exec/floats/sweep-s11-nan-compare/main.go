package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group J: every comparison operator against a
// NaN (spec#Comparison_operators: NaN is unordered — == < <= > >= all false, != true), on the left,
// on the right and on both sides, at float64 and float32, against ±Inf and -0, the negated forms
// (`!(a < b)` is not `a >= b`), in a switch, a payload NaN, a defined float type, and the
// non-NaN controls. Site floatCompareResult (fcmp64 / fcmp32).

import "math"

type dF float64

func nanLeft64() (bool, bool, bool, bool, bool, bool) {
	z := 0.0
	nan := z / z
	var one float64 = 1
	return nan == one, nan != one, nan < one, nan <= one, nan > one, nan >= one
}

func nanRight64() (bool, bool, bool, bool, bool, bool) {
	z := 0.0
	nan := z / z
	var one float64 = 1
	return one == nan, one != nan, one < nan, one <= nan, one > nan, one >= nan
}

func nanBoth64() (bool, bool, bool, bool, bool, bool) {
	z := 0.0
	nan := z / z
	nan2 := z / z
	return nan == nan2, nan != nan2, nan < nan2, nan <= nan2, nan > nan2, nan >= nan2
}

func nanLeft32() (bool, bool, bool, bool, bool, bool) {
	var z float32 = 0
	nan := z / z
	var one float32 = 1
	return nan == one, nan != one, nan < one, nan <= one, nan > one, nan >= one
}

func nanRight32() (bool, bool, bool, bool, bool, bool) {
	var z float32 = 0
	nan := z / z
	var one float32 = 1
	return one == nan, one != nan, one < nan, one <= nan, one > nan, one >= nan
}

func nanBoth32() (bool, bool, bool, bool, bool, bool) {
	var z float32 = 0
	nan := z / z
	nan2 := z / z
	return nan == nan2, nan != nan2, nan < nan2, nan <= nan2, nan > nan2, nan >= nan2
}

func nanVersusSpecials() (bool, bool, bool, bool, bool, bool, bool, bool) {
	z := 0.0
	nan := z / z
	var one float64 = 1
	inf := one / z
	nz := -z
	return nan < inf, nan > -inf, nan <= inf, nan >= -inf, nan == nz, nan != nz, nz < nan, inf > nan
}

func nanNegatedForms() (bool, bool, bool, bool, bool, bool) {
	z := 0.0
	nan := z / z
	var one float64 = 1
	return !(nan < one), nan >= one, !(nan == one), nan != one, !(one <= nan), one > nan
}

func nanSwitch() (int, int, int) {
	z := 0.0
	nan := z / z
	var one float64 = 1
	a := 0
	switch {
	case nan < one:
		a = 1
	case nan > one:
		a = 2
	case nan == one:
		a = 3
	default:
		a = 4
	}
	b := 0
	switch {
	case nan != nan:
		b = 1
	default:
		b = 2
	}
	c := 0
	if nan < one || nan >= one {
		c = 1
	} else {
		c = 2
	}
	return a, b, c
}

func nanPayloadCompare() (bool, bool, bool, bool, bool, bool, bool) {
	n := math.Float64frombits(0x7FF0000000000001)
	m := math.Float64frombits(0xFFF8000000000001)
	var one float64 = 1
	return n == n, n != m, n < one, n >= one, m > one, m <= one, n == m
}

func nanDefinedAndControls() (bool, bool, bool, bool, bool, bool, bool) {
	var z dF = 0
	nan := z / z
	var one dF = 1
	var x float64 = 2.5
	var y float32 = 2.5
	return nan == nan, nan != one, nan < one, x != x, y != y, x == x, y >= y
}

func main() {
	nanLeft64()
	nanRight64()
	nanBoth64()
	nanLeft32()
	nanRight32()
	nanBoth32()
	nanVersusSpecials()
	nanNegatedForms()
	nanSwitch()
	nanPayloadCompare()
	nanDefinedAndControls()
}
