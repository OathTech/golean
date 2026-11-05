package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group P: int ↔ float ROUND TRIPS in range —
// the precision lost above 2^53 (int64 → float64 → int64), float64 → int64 → float64 of fractions
// and of -0 (which comes back as +0), the uint64 ≥ 2^63 path both ways, the narrow kinds through
// float32. The out-of-range trips (uint64 max through float64, int32 max through float32) are R6's
// designed refusal: probed, not rowed. Sites convertValueToTy's float→int and int→float arms.

import "math"

func roundTripInt64(a, b, c int64) (int64, int64, int64, int64, int64, int64) {
	var mn int64 = -9223372036854775808
	var d int64 = 4611686018427387905
	var e int64 = -9007199254740993
	return int64(float64(a)), int64(float64(b)), int64(float64(c)), int64(float64(mn)), int64(float64(d)), int64(float64(e))
}

func roundTripFloat64() (uint64, uint64, uint64, uint64, uint64) {
	var a float64 = -2.9
	var b float64 = 4503599627370496.5
	var c float64 = 1e15 + 0.75
	z := 0.0
	nz := -z
	var d float64 = -0.999
	return math.Float64bits(float64(int64(a))), math.Float64bits(float64(int64(b))), math.Float64bits(float64(int64(c))),
		math.Float64bits(float64(int64(nz))), math.Float64bits(float64(int8(d)))
}

func roundTripUint64() (uint64, uint64, uint64, uint64) {
	var a uint64 = 18446744073709549568
	var b uint64 = 9223372036854777856
	var c uint64 = 9223372036854775808
	var d uint64 = 9223372036854775809 // rounds to 2^63 at float64
	return uint64(float64(a)), uint64(float64(b)), uint64(float64(c)), uint64(float64(d))
}

func roundTripNarrow() (int32, int8, int16, uint16, int8, uint8, int32) {
	var a int32 = 2147483520
	var b int8 = -128
	var c int16 = 32767
	var d uint16 = 65535
	var e int8 = 127
	var f uint8 = 255
	var g int32 = 16777217 // rounds to 16777216 at float32
	return int32(float32(a)), int8(float32(b)), int16(float32(c)), uint16(float32(d)), int8(float64(e)), uint8(float32(f)), int32(float32(g))
}

func main() {
	roundTripInt64(9007199254740992, 9007199254740993, 9007199254740995)
	roundTripFloat64()
	roundTripUint64()
	roundTripNarrow()
}
