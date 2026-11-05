package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group K: `min`/`max` at the extremes of EVERY
// integer kind (returning the kind), with constants mixed in, and over floats with a NaN in every
// position of a three-argument call, ±0 ties in three arguments and at float32, infinities, a
// single NaN argument, payload NaNs through the three-argument fold (gc chains its MINSD/POR idiom
// left to right), untyped constant arguments adapted to float32, a defined float type. A result
// that is a machine-produced NaN is observed by its self-inequality (its bits are BUG-094's
// refusal). Sites minOf/maxOf → floatMinMaxBits, valueLess.

import "math"

type dF float64

func minMaxInt8() (int8, int8, int8, int8) {
	var mx int8 = 127
	var mn int8 = -128
	var z int8 = 0
	return min(mx, mn), max(mx, mn), min(mx, z, mn), max(mn, z, mx)
}

func minMaxInt16() (int16, int16, int16, int16) {
	var mx int16 = 32767
	var mn int16 = -32768
	var z int16 = 0
	return min(mx, mn), max(mx, mn), min(mx, z, mn), max(mn, z, mx)
}

func minMaxInt32() (int32, int32, int32, int32) {
	var mx int32 = 2147483647
	var mn int32 = -2147483648
	var z int32 = 0
	return min(mx, mn), max(mx, mn), min(mx, z, mn), max(mn, z, mx)
}

func minMaxInt64() (int64, int64, int64, int64) {
	var mx int64 = 9223372036854775807
	var mn int64 = -9223372036854775808
	var z int64 = 0
	return min(mx, mn), max(mx, mn), min(mx, z, mn), max(mn, z, mx)
}

func minMaxInt() (int, int, int, int) {
	var mx int = 9223372036854775807
	var mn int = -9223372036854775808
	var z int = 0
	return min(mx, mn), max(mx, mn), min(mx, z, mn), max(mn, z, mx)
}

func minMaxUint8() (uint8, uint8, uint8, uint8) {
	var mx uint8 = 255
	var one uint8 = 1
	var z uint8 = 0
	return min(mx, z), max(mx, z), min(mx, one, z), max(z, one, mx)
}

func minMaxUint16() (uint16, uint16, uint16, uint16) {
	var mx uint16 = 65535
	var one uint16 = 1
	var z uint16 = 0
	return min(mx, z), max(mx, z), min(mx, one, z), max(z, one, mx)
}

func minMaxUint32() (uint32, uint32, uint32, uint32) {
	var mx uint32 = 4294967295
	var one uint32 = 1
	var z uint32 = 0
	return min(mx, z), max(mx, z), min(mx, one, z), max(z, one, mx)
}

func minMaxUint64() (uint64, uint64, uint64, uint64) {
	var mx uint64 = 18446744073709551615
	var one uint64 = 1
	var z uint64 = 0
	return min(mx, z), max(mx, z), min(mx, one, z), max(z, one, mx)
}

func minMaxUint() (uint, uint, uint, uint) {
	var mx uint = 18446744073709551615
	var one uint = 1
	var z uint = 0
	return min(mx, z), max(mx, z), min(mx, one, z), max(z, one, mx)
}

func minMaxUintptr() (uint64, uint64, uint64, uint64) {
	var mx uintptr = 18446744073709551615
	var one uintptr = 1
	var z uintptr = 0
	return uint64(min(mx, z)), uint64(max(mx, z)), uint64(min(mx, one, z)), uint64(max(z, one, mx))
}

func minMaxConstantsMixed() (int64, uint8, int8, int64, uint64) {
	var x int64 = 1 << 41
	var u uint8 = 3
	var i int8 = -5
	var big uint64 = 1<<64 - 1
	return min(x, 1<<40), max(u, 255), min(i, -128), max(x, -1<<63), min(big, 1<<63)
}

func minMaxNaNPositions() (bool, bool, bool, bool, bool, bool, bool, bool, bool) {
	z := 0.0
	nan := z / z
	var one float64 = 1
	var two float64 = 2
	inf := one / z
	r1 := min(one, nan, two)
	r2 := max(nan, one, two)
	r3 := min(one, two, nan)
	r4 := max(one, nan)
	r5 := min(nan)
	r6 := max(nan, nan)
	r7 := min(inf, nan)
	r8 := max(-inf, nan)
	r9 := min(nan, -inf, inf)
	return r1 != r1, r2 != r2, r3 != r3, r4 != r4, r5 != r5, r6 != r6, r7 != r7, r8 != r8, r9 != r9
}

func minMaxNaNPositions32() (bool, bool, bool, bool, bool) {
	var z float32 = 0
	nan := z / z
	var one float32 = 1
	var two float32 = 2
	r1 := min(one, nan, two)
	r2 := max(nan, one, two)
	r3 := min(one, two, nan)
	r4 := max(two, nan)
	r5 := min(nan)
	return r1 != r1, r2 != r2, r3 != r3, r4 != r4, r5 != r5
}

func minMaxSignedZeros3() (uint64, uint64, uint64, uint64, uint64, uint64) {
	z := 0.0
	nz := -z
	return math.Float64bits(min(z, nz, z)), math.Float64bits(max(nz, z, nz)), math.Float64bits(min(nz, z, nz)),
		math.Float64bits(max(z, nz, z)), math.Float64bits(min(z, z, nz)), math.Float64bits(max(nz, nz, z))
}

func minMaxSignedZeros32() (uint32, uint32, uint32, uint32, uint32, uint32) {
	var z float32 = 0
	nz := -z
	return math.Float32bits(min(z, nz)), math.Float32bits(min(nz, z)), math.Float32bits(max(z, nz)),
		math.Float32bits(max(nz, z)), math.Float32bits(min(z, nz, z)), math.Float32bits(max(nz, z, nz))
}

func minMaxInfinities() (uint64, uint64, uint64, uint64, uint64, uint64, uint32, uint32) {
	z := 0.0
	var one float64 = 1
	inf := one / z
	var z32 float32 = 0
	var one32 float32 = 1
	inf32 := one32 / z32
	return math.Float64bits(min(inf, one)), math.Float64bits(max(inf, one)), math.Float64bits(min(-inf, one)),
		math.Float64bits(max(-inf, one)), math.Float64bits(min(inf, -inf)), math.Float64bits(max(inf, -inf)),
		math.Float32bits(min(inf32, one32)), math.Float32bits(max(-inf32, one32))
}

func minMaxPayload3Args() (uint64, uint64, uint64, uint64, uint32, uint32) {
	n := math.Float64frombits(0x7FF8000000000001)
	s := math.Float64frombits(0x7FF0000000000001)
	var one float64 = 1
	var two float64 = 2
	n32 := math.Float32frombits(0x7FC00001)
	var one32 float32 = 1
	var two32 float32 = 2
	return math.Float64bits(min(n, one, two)), math.Float64bits(min(one, n, two)), math.Float64bits(max(one, two, n)),
		math.Float64bits(min(n, s, one)), math.Float32bits(min(one32, n32, two32)), math.Float32bits(max(n32, one32, two32))
}

func minMaxUntypedAt32() (uint32, uint32, uint32, uint64) {
	var x float32 = 0.1
	var y float32 = 0.3
	var f float64 = 0.1
	return math.Float32bits(min(x, 0.1)), math.Float32bits(max(y, 0.3)), math.Float32bits(min(x, 1<<24+1)), math.Float64bits(max(f, 0.1))
}

func minMaxDefinedFloat() (bool, uint64, uint64) {
	var z dF = 0
	nan := z / z
	nz := -z
	var one dF = 1
	r := min(one, nan)
	return r != r, math.Float64bits(float64(min(z, nz))), math.Float64bits(float64(max(nz, z)))
}

func main() {
	minMaxInt8()
	minMaxInt16()
	minMaxInt32()
	minMaxInt64()
	minMaxInt()
	minMaxUint8()
	minMaxUint16()
	minMaxUint32()
	minMaxUint64()
	minMaxUint()
	minMaxUintptr()
	minMaxConstantsMixed()
	minMaxNaNPositions()
	minMaxNaNPositions32()
	minMaxSignedZeros3()
	minMaxSignedZeros32()
	minMaxInfinities()
	minMaxPayload3Args()
	minMaxUntypedAt32()
	minMaxDefinedFloat()
}
