package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group G: int → float conversions observed as
// BIT PATTERNS (spec#Conversions: rounded to the nearest, ties to even — IEEE 754 round-to-even)
// at the magnitudes where rounding happens: 2^53 and 2^63 neighbours (float64), 2^24 and 2^63
// neighbours (float32, a SINGLE rounding — never via float64), the uint64 ≥ 2^63 path, the
// extremes of every kind. Run-time sources. Site convertValueToTy's int→float arm (ratToBits).
import "math"

func f64OfInt64N0() uint64 {
	var x int64 = 9223372036854775807
	return math.Float64bits(float64(x))
}

func f64OfInt64N1() uint64 {
	var x int64 = -9223372036854775808
	return math.Float64bits(float64(x))
}

func f64OfUint64N2() uint64 {
	var x uint64 = 18446744073709551615
	return math.Float64bits(float64(x))
}

func f64OfUint64N3() uint64 {
	var x uint64 = 9223372036854775808
	return math.Float64bits(float64(x))
}

func f64OfUint64N4() uint64 {
	var x uint64 = 9223372036854775809
	return math.Float64bits(float64(x))
}

func f64OfUint64N5() uint64 {
	var x uint64 = 9223372036854776832
	return math.Float64bits(float64(x))
}

func f64OfUint64N6() uint64 {
	var x uint64 = 9223372036854776833
	return math.Float64bits(float64(x))
}

func f64OfUint64N7() uint64 {
	var x uint64 = 9223372036854778880
	return math.Float64bits(float64(x))
}

func f64OfUint64N8() uint64 {
	var x uint64 = 9223372036854777855
	return math.Float64bits(float64(x))
}

func f64OfInt64N9() uint64 {
	var x int64 = 9007199254740993
	return math.Float64bits(float64(x))
}

func f64OfInt64N10() uint64 {
	var x int64 = 9007199254740994
	return math.Float64bits(float64(x))
}

func f64OfInt64N11() uint64 {
	var x int64 = 9007199254740995
	return math.Float64bits(float64(x))
}

func f64OfInt64N12() uint64 {
	var x int64 = 9007199254740997
	return math.Float64bits(float64(x))
}

func f64OfInt64N13() uint64 {
	var x int64 = -9007199254740993
	return math.Float64bits(float64(x))
}

func f64OfInt64N14() uint64 {
	var x int64 = -9007199254740995
	return math.Float64bits(float64(x))
}

func f64OfUint32N15() uint64 {
	var x uint32 = 4294967295
	return math.Float64bits(float64(x))
}

func f64OfInt32N16() uint64 {
	var x int32 = -2147483648
	return math.Float64bits(float64(x))
}

func f64OfInt8N17() uint64 {
	var x int8 = -128
	return math.Float64bits(float64(x))
}

func f64OfInt16N18() uint64 {
	var x int16 = 32767
	return math.Float64bits(float64(x))
}

func f64OfUint8N19() uint64 {
	var x uint8 = 255
	return math.Float64bits(float64(x))
}

func f64OfUintptrN20() uint64 {
	var x uintptr = 18446744073709551615
	return math.Float64bits(float64(x))
}

func f64OfIntN21() uint64 {
	var x int = -9223372036854775807
	return math.Float64bits(float64(x))
}

func f32OfInt32N0() uint32 {
	var x int32 = 16777217
	return math.Float32bits(float32(x))
}

func f32OfInt32N1() uint32 {
	var x int32 = 16777218
	return math.Float32bits(float32(x))
}

func f32OfInt32N2() uint32 {
	var x int32 = 16777219
	return math.Float32bits(float32(x))
}

func f32OfInt32N3() uint32 {
	var x int32 = -16777217
	return math.Float32bits(float32(x))
}

func f32OfInt64N4() uint32 {
	var x int64 = 9223372036854775807
	return math.Float32bits(float32(x))
}

func f32OfUint64N5() uint32 {
	var x uint64 = 18446744073709551615
	return math.Float32bits(float32(x))
}

func f32OfUint64N6() uint32 {
	var x uint64 = 9223372586610589696
	return math.Float32bits(float32(x))
}

func f32OfUint64N7() uint32 {
	var x uint64 = 9223372586610589697
	return math.Float32bits(float32(x))
}

func f32OfInt32N8() uint32 {
	var x int32 = -2147483648
	return math.Float32bits(float32(x))
}

func f32OfUint32N9() uint32 {
	var x uint32 = 4294967295
	return math.Float32bits(float32(x))
}

func f32OfInt64N10() uint32 {
	var x int64 = 9007199791611905
	return math.Float32bits(float32(x))
}

func f32OfInt64N11() uint32 {
	var x int64 = -9007199791611905
	return math.Float32bits(float32(x))
}

func f32OfInt16N12() uint32 {
	var x int16 = -32768
	return math.Float32bits(float32(x))
}

func f32OfUint16N13() uint32 {
	var x uint16 = 65535
	return math.Float32bits(float32(x))
}

func f32OfUintptrN14() uint32 {
	var x uintptr = 16777217
	return math.Float32bits(float32(x))
}

func f32OfIntN15() uint32 {
	var x int = 16777221
	return math.Float32bits(float32(x))
}

type dInt int
type dRune rune

func floatOfDefinedAndRune() (uint64, uint32, uint64) {
	var a dInt = 9007199254740993
	var r dRune = -2147483648
	var b rune = 16777217
	return math.Float64bits(float64(a)), math.Float32bits(float32(r)), math.Float64bits(float64(b))
}

func floatOfConstants() (uint64, uint32, uint64, uint32) {
	return math.Float64bits(float64(1<<63 - 1)), math.Float32bits(float32(1<<63 - 1)), math.Float64bits(float64(9007199254740993)), math.Float32bits(float32(16777217))
}

func main() {
	f64OfInt64N0()
	f64OfInt64N1()
	f64OfUint64N2()
	f64OfUint64N3()
	f64OfUint64N4()
	f64OfUint64N5()
	f64OfUint64N6()
	f64OfUint64N7()
	f64OfUint64N8()
	f64OfInt64N9()
	f64OfInt64N10()
	f64OfInt64N11()
	f64OfInt64N12()
	f64OfInt64N13()
	f64OfInt64N14()
	f64OfUint32N15()
	f64OfInt32N16()
	f64OfInt8N17()
	f64OfInt16N18()
	f64OfUint8N19()
	f64OfUintptrN20()
	f64OfIntN21()
	f32OfInt32N0()
	f32OfInt32N1()
	f32OfInt32N2()
	f32OfInt32N3()
	f32OfInt64N4()
	f32OfUint64N5()
	f32OfUint64N6()
	f32OfUint64N7()
	f32OfInt32N8()
	f32OfUint32N9()
	f32OfInt64N10()
	f32OfInt64N11()
	f32OfInt16N12()
	f32OfUint16N13()
	f32OfUintptrN14()
	f32OfIntN15()
	floatOfDefinedAndRune()
	floatOfConstants()
}
