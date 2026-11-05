package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group A: wrap-around arithmetic at EVERY
// integer width (spec#Integer_overflow: the result wraps, no panic; the most negative value's
// negation and its quotient by -1 are itself). The extremes are run-time VARIABLES so no
// constant overflow is folded or rejected; uintptr results are observed through uint64.
func wrapInt8() (int8, int8, int8, int8, int8, int8, int8, int8) {
	var mx int8 = 127
	var mn int8 = -128
	var two int8 = 2
	a := mx + 1
	b := mn - 1
	c := mx * two
	d := mx * mx
	e := -mn
	f := mn / -1
	g := mn % -1
	h := (mx + 1) + (mx + 1)
	return a, b, c, d, e, f, g, h
}

func wrapInt16() (int16, int16, int16, int16, int16, int16, int16, int16) {
	var mx int16 = 32767
	var mn int16 = -32768
	var two int16 = 2
	a := mx + 1
	b := mn - 1
	c := mx * two
	d := mx * mx
	e := -mn
	f := mn / -1
	g := mn % -1
	h := (mx + 1) + (mx + 1)
	return a, b, c, d, e, f, g, h
}

func wrapInt32() (int32, int32, int32, int32, int32, int32, int32, int32) {
	var mx int32 = 2147483647
	var mn int32 = -2147483648
	var two int32 = 2
	a := mx + 1
	b := mn - 1
	c := mx * two
	d := mx * mx
	e := -mn
	f := mn / -1
	g := mn % -1
	h := (mx + 1) + (mx + 1)
	return a, b, c, d, e, f, g, h
}

func wrapInt64() (int64, int64, int64, int64, int64, int64, int64, int64) {
	var mx int64 = 9223372036854775807
	var mn int64 = -9223372036854775808
	var two int64 = 2
	a := mx + 1
	b := mn - 1
	c := mx * two
	d := mx * mx
	e := -mn
	f := mn / -1
	g := mn % -1
	h := (mx + 1) + (mx + 1)
	return a, b, c, d, e, f, g, h
}

func wrapInt() (int, int, int, int, int, int, int, int) {
	var mx int = 9223372036854775807
	var mn int = -9223372036854775808
	var two int = 2
	a := mx + 1
	b := mn - 1
	c := mx * two
	d := mx * mx
	e := -mn
	f := mn / -1
	g := mn % -1
	h := (mx + 1) + (mx + 1)
	return a, b, c, d, e, f, g, h
}

func wrapUint8() (uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8) {
	var mx uint8 = 255
	var z uint8 = 0
	var two uint8 = 2
	a := z - 1
	b := mx + 1
	c := mx * mx
	d := -mx
	e := mx * two
	f := -z - 1
	g := mx + mx
	h := (z - 1) / two
	return a, b, c, d, e, f, g, h
}

func wrapUint16() (uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16) {
	var mx uint16 = 65535
	var z uint16 = 0
	var two uint16 = 2
	a := z - 1
	b := mx + 1
	c := mx * mx
	d := -mx
	e := mx * two
	f := -z - 1
	g := mx + mx
	h := (z - 1) / two
	return a, b, c, d, e, f, g, h
}

func wrapUint32() (uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32) {
	var mx uint32 = 4294967295
	var z uint32 = 0
	var two uint32 = 2
	a := z - 1
	b := mx + 1
	c := mx * mx
	d := -mx
	e := mx * two
	f := -z - 1
	g := mx + mx
	h := (z - 1) / two
	return a, b, c, d, e, f, g, h
}

func wrapUint64() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	var mx uint64 = 18446744073709551615
	var z uint64 = 0
	var two uint64 = 2
	a := z - 1
	b := mx + 1
	c := mx * mx
	d := -mx
	e := mx * two
	f := -z - 1
	g := mx + mx
	h := (z - 1) / two
	return a, b, c, d, e, f, g, h
}

func wrapUint() (uint, uint, uint, uint, uint, uint, uint, uint) {
	var mx uint = 18446744073709551615
	var z uint = 0
	var two uint = 2
	a := z - 1
	b := mx + 1
	c := mx * mx
	d := -mx
	e := mx * two
	f := -z - 1
	g := mx + mx
	h := (z - 1) / two
	return a, b, c, d, e, f, g, h
}

func wrapUintptr() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	var mx uintptr = 18446744073709551615
	var z uintptr = 0
	var two uintptr = 2
	a := z - 1
	b := mx + 1
	c := mx * mx
	d := -mx
	e := mx * two
	f := -z - 1
	g := mx + mx
	h := (z - 1) / two
	return uint64(a), uint64(b), uint64(c), uint64(d), uint64(e), uint64(f), uint64(g), uint64(h)
}

type dInt8 int8
type dUint16 uint16
type dInt64 int64
type dUint64 uint64

func wrapByte() (byte, byte, byte, byte) {
	var mx byte = 255
	var z byte = 0
	return mx + 1, z - 1, mx * mx, -mx
}

func wrapRune() (rune, rune, rune, rune) {
	var mx rune = 2147483647
	var mn rune = -2147483648
	return mx + 1, mn - 1, -mn, mn / -1
}

func wrapDInt8() (dInt8, dInt8, dInt8, dInt8, dInt8, dInt8) {
	var mx dInt8 = 127
	var mn dInt8 = -128
	return mx + 1, mn - 1, mx * 2, -mn, mn / -1, mn % -1
}

func wrapDUint16() (dUint16, dUint16, dUint16, dUint16) {
	var mx dUint16 = 65535
	var z dUint16 = 0
	return mx + 1, z - 1, mx * mx, -mx
}

func wrapDInt64() (dInt64, dInt64, dInt64, dInt64, dInt64, dInt64) {
	var mx dInt64 = 9223372036854775807
	var mn dInt64 = -9223372036854775808
	return mx + 1, mn - 1, mx * 2, -mn, mn / -1, mn % -1
}

func wrapDUint64() (dUint64, dUint64, dUint64, dUint64) {
	var mx dUint64 = 18446744073709551615
	var z dUint64 = 0
	return mx + 1, z - 1, mx * mx, -mx
}

func wrapCompoundInt8() (int8, int8, int8, int8) {
	var a int8 = 127
	a += 1
	var b int8 = -128
	b -= 1
	var c int8 = 64
	c *= 2
	var d int8 = -128
	d /= -1
	return a, b, c, d
}

func wrapCompoundUint8() (uint8, uint8, uint8, uint8) {
	var a uint8 = 255
	a += 1
	var b uint8 = 0
	b -= 1
	var c uint8 = 128
	c *= 2
	var d uint8 = 255
	d *= 255
	return a, b, c, d
}

func wrapCompoundInt64() (int64, int64, int64, int64) {
	var a int64 = 9223372036854775807
	a += 1
	var b int64 = -9223372036854775808
	b -= 1
	var c int64 = 4611686018427387904
	c *= 2
	var d int64 = -9223372036854775808
	d %= -1
	return a, b, c, d
}

func wrapCompoundUint64() (uint64, uint64, uint64, uint64) {
	var a uint64 = 18446744073709551615
	a += 1
	var b uint64 = 0
	b -= 1
	var c uint64 = 9223372036854775808
	c *= 2
	var d uint64 = 18446744073709551615
	d *= 18446744073709551615
	return a, b, c, d
}

func main() {
	wrapInt8()
	wrapInt16()
	wrapInt32()
	wrapInt64()
	wrapInt()
	wrapUint8()
	wrapUint16()
	wrapUint32()
	wrapUint64()
	wrapUint()
	wrapUintptr()
	wrapByte()
	wrapRune()
	wrapDInt8()
	wrapDUint16()
	wrapDInt64()
	wrapDUint64()
	wrapCompoundInt8()
	wrapCompoundUint8()
	wrapCompoundInt64()
	wrapCompoundUint64()
}
