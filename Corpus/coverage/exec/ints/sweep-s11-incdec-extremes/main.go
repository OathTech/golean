package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group M: `++` at the maximum and `--` at the
// minimum of EVERY integer kind (the IncDec desugar's synthetic 1 at the operand's kind, BUG-042's
// site), at the aliases and at defined kinds, and through a struct field, an array element, a
// slice element, a map value (the map compound desugar) and a pointer.
import "math"

func incDecInt8() (int8, int8) {
	var a int8 = 127
	a++
	var b int8 = -128
	b--
	return a, b
}

func incDecInt16() (int16, int16) {
	var a int16 = 32767
	a++
	var b int16 = -32768
	b--
	return a, b
}

func incDecInt32() (int32, int32) {
	var a int32 = 2147483647
	a++
	var b int32 = -2147483648
	b--
	return a, b
}

func incDecInt64() (int64, int64) {
	var a int64 = 9223372036854775807
	a++
	var b int64 = -9223372036854775808
	b--
	return a, b
}

func incDecInt() (int, int) {
	var a int = 9223372036854775807
	a++
	var b int = -9223372036854775808
	b--
	return a, b
}

func incDecUint8() (uint8, uint8) {
	var a uint8 = 255
	a++
	var b uint8 = 0
	b--
	return a, b
}

func incDecUint16() (uint16, uint16) {
	var a uint16 = 65535
	a++
	var b uint16 = 0
	b--
	return a, b
}

func incDecUint32() (uint32, uint32) {
	var a uint32 = 4294967295
	a++
	var b uint32 = 0
	b--
	return a, b
}

func incDecUint64() (uint64, uint64) {
	var a uint64 = 18446744073709551615
	a++
	var b uint64 = 0
	b--
	return a, b
}

func incDecUint() (uint, uint) {
	var a uint = 18446744073709551615
	a++
	var b uint = 0
	b--
	return a, b
}

func incDecUintptr() (uint64, uint64) {
	var a uintptr = 18446744073709551615
	a++
	var b uintptr = 0
	b--
	return uint64(a), uint64(b)
}

type dInt int
type dUint uint
type dUintptr uintptr
type dInt16 int16
type dUint32 uint32

func incDecDefined() (dInt, dUint, uint64, dInt16, dUint32) {
	var a dInt = 9223372036854775807
	a++
	var b dUint = 0
	b--
	var c dUintptr = 18446744073709551615
	c++
	var d dInt16 = -32768
	d--
	var e dUint32 = 4294967295
	e++
	return a, b, uint64(c), d, e
}

func incDecAliases() (byte, rune, byte, rune) {
	var a byte = 255
	a++
	var b rune = 2147483647
	b++
	var c byte = 0
	c--
	var d rune = -2147483648
	d--
	return a, b, c, d
}

type holder struct {
	u8  uint8
	i64 int64
	u64 uint64
	i8  int8
}

func incDecField() (uint8, int64, uint64, int8) {
	h := holder{u8: 255, i64: 9223372036854775807, u64: 0, i8: -128}
	h.u8++
	h.i64++
	h.u64--
	h.i8--
	return h.u8, h.i64, h.u64, h.i8
}

func incDecElements() (uint16, int32, int8, uint64) {
	arr := [2]uint16{65535, 1}
	arr[0]++
	sl := []int32{-2147483648}
	sl[0]--
	m := map[string]int8{"k": -128}
	m["k"]--
	m2 := map[int]uint64{1: 18446744073709551615}
	m2[1]++
	return arr[0], sl[0], m["k"], m2[1]
}

func incDecPointer() (int8, uint32) {
	var a int8 = 127
	p := &a
	*p++
	var b uint32 = 0
	q := &b
	*q--
	return a, b
}

func incDecFloatsAbsorbed() (uint64, uint32, uint64) {
	var f float64 = 9007199254740992
	f++
	var g float32 = -16777216
	g--
	var h float64 = 9007199254740991
	h++
	h++
	return math.Float64bits(f), math.Float32bits(g), math.Float64bits(h)
}

func main() {
	incDecInt8()
	incDecInt16()
	incDecInt32()
	incDecInt64()
	incDecInt()
	incDecUint8()
	incDecUint16()
	incDecUint32()
	incDecUint64()
	incDecUint()
	incDecUintptr()
	incDecDefined()
	incDecAliases()
	incDecField()
	incDecElements()
	incDecPointer()
	incDecFloatsAbsorbed()
}
