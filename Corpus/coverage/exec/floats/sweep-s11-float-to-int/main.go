package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group F1: float → int conversions IN RANGE at
// every integer target kind from float64 and float32 sources (spec#Conversions: the fraction is
// discarded, truncation toward zero); the largest float below each power-of-two bound, the exact
// bounds, -0.5 and -0 (the truncation 0 is representable), a denormal, a rounded float32 source,
// defined source and target types. The out-of-range / NaN / Inf cells are R6's designed refusal
// (floats/to-int-out-of-range) and are probed, not rowed. Site convertValueToTy's float→int arm.

type dFloat float64
type dInt16 int16

func truncF64ToSigned() (int8, int8, int16, int16, int32, int32, int64, int64, int, int64) {
	var a float64 = 127.99
	var b float64 = -128.99
	var c float64 = 32767.5
	var d float64 = -32768.75
	var e float64 = 2147483647.0
	var f float64 = -2147483648.9
	var g float64 = 9223372036854774784 // the largest float64 below 2^63
	var h float64 = -9223372036854775808
	z := 0.0
	nz := -z
	var j float64 = 1e15 + 0.5
	return int8(a), int8(b), int16(c), int16(d), int32(e), int32(f), int64(g), int64(h), int(nz), int64(j)
}

func truncF64ToUnsigned() (uint8, uint8, uint8, uint16, uint32, uint64, uint64, uint64, uint, uint64) {
	var a float64 = 255.9
	var b float64 = -0.5
	var c float64 = 0.999
	var d float64 = 65535.99
	var e float64 = 4294967295.5
	var f float64 = 18446744073709549568 // the largest float64 below 2^64
	var g float64 = 9223372036854775808  // 2^63 exactly
	var h float64 = 9223372036854777856  // 2^63 + 2048
	var i float64 = 1e19
	var j float64 = 5e-324
	var p uintptr = uintptr(e)
	_ = p
	return uint8(a), uint8(b), uint8(c), uint16(d), uint32(e), uint64(f), uint64(g), uint64(h), uint(i), uint64(j)
}

func truncF64ExactBounds() (int8, int8, int16, int16, int32, int32, uint8, uint16, uint32, uint64) {
	var a float64 = -128
	var b float64 = 127
	var c float64 = -32768
	var d float64 = 32767
	var e float64 = -2147483648
	var f float64 = 2147483647
	var g float64 = 255
	var h float64 = 65535
	var i float64 = 4294967295
	var j float64 = 9007199254740992
	return int8(a), int8(b), int16(c), int16(d), int32(e), int32(f), uint8(g), uint16(h), uint32(i), uint64(j)
}

func truncF32ToInts() (int8, int16, int32, int32, int64, uint8, uint16, uint32, uint64, int) {
	var a float32 = 127.9
	var b float32 = -32768.5
	var c float32 = 2147483520 // the largest float32 below 2^31
	var d float32 = -2147483648
	var e float32 = 9223371487098961920 // the largest float32 below 2^63
	var f float32 = 255.5
	var g float32 = 65535.5
	var h float32 = 4294967040 // the largest float32 below 2^32
	var i float32 = 18446742974197923840 // the largest float32 below 2^64
	var j float32 = 16777217 // rounds to 16777216 at float32
	return int8(a), int16(b), int32(c), int32(d), int64(e), uint8(f), uint16(g), uint32(h), uint64(i), int(j)
}

func truncUintptrTargets() (uint64, uint64, uint64) {
	var a float64 = 18446744073709549568
	var b float32 = -0.75
	var c float64 = 4294967295.5
	return uint64(uintptr(a)), uint64(uintptr(b)), uint64(uintptr(c))
}

func truncDefined() (dInt16, int, uint8, dInt16) {
	var a dFloat = -300.7
	var b float32 = 12.5
	var c dFloat = 200.2
	var d float64 = 32767.9
	return dInt16(a), int(b), uint8(c), dInt16(d)
}

func main() {
	truncF64ToSigned()
	truncF64ToUnsigned()
	truncF64ExactBounds()
	truncF32ToInts()
	truncUintptrTargets()
	truncDefined()
}
