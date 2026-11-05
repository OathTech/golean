package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group L: constant expressions AT the kind
// boundaries — typed constants at every kind's extremes, untyped arithmetic beyond 64 bits folded
// back into a kind (gc folds exactly; the wire carries the folded value, emitConstValue's kind),
// untyped integer constants representable only as floats (`var f float64 = 1 << 70` is LEGAL), a
// float constant count and index (legal when representable as an integer), the exact rationals of
// decimal literals at both widths, constant division and modulo signs, and the DEFAULT types of
// untyped constants observed through the readout's kind tag. The rejections (overflowing constants)
// are the negative rows constants/sweep-s11-*. Sites emitConstValue, the decoder's "int"/"float" arms.

import "math"

func typedConstantExtremes() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var a int8 = -128
	var b int16 = -32768
	var c int32 = -1 << 31
	var d int64 = -1 << 63
	var e int = 1<<63 - 1
	var f uint8 = 1<<8 - 1
	var g uint16 = 65535
	var h uint32 = 1<<32 - 1
	var i uint64 = 1<<64 - 1
	var j uint = 1<<64 - 1
	var k uintptr = 1<<64 - 1
	return a, b, c, d, e, f, g, h, i, j, uint64(k)
}

func constantFolding() (int, uint64, int64, int, int64, int8, int8, uint8, int8) {
	const big = 1 << 70
	const q int8 = -7 / 2
	const r int8 = -7 % 2
	const c uint8 = 1 << 7
	const n int8 = -1 << 7
	return (big + 1) % 7, 1<<64 - 1, -(1 << 63), big >> 60, (1 << 100) / (1 << 90), q, r, c, n
}

func constantsIntoFloats() (uint64, uint32, uint64, uint64, uint64, uint32, uint64, uint32) {
	var f float64 = 1 << 70
	var g float32 = 1 << 100
	var h float64 = 1 << 511
	const q = 1e400
	var i float64 = q / 1e300
	var j float64 = 9007199254740993
	var k float32 = 16777217
	var l float64 = 1 << 53 + 1
	var m float32 = 1 << 24 + 1
	return math.Float64bits(f), math.Float32bits(g), math.Float64bits(h), math.Float64bits(i), math.Float64bits(j), math.Float32bits(k), math.Float64bits(l), math.Float32bits(m)
}

func floatLiteralRationals() (uint64, uint32, uint64, uint32, uint64, uint32, uint64, uint64) {
	return math.Float64bits(0.1), math.Float32bits(0.1), math.Float64bits(1e23), math.Float32bits(1e23),
		math.Float64bits(2.0 / 3), math.Float32bits(2.0 / 3), math.Float64bits(1.0 / 10 * 3), math.Float64bits(0.1 * 3)
}

func floatConstantCountAndIndex() (int, int, byte, int) {
	x := 1 << 2.0
	y := 1 << 3.0
	s := "abc"
	arr := [4]int{10, 20, 30, 40}
	return x, y, s[1.0], arr[2.0]
}

func untypedDefaults() (int, int, int, rune, float64, float64, float64, rune, int, int, rune, int, float64, uint8) {
	a := 1 << 40
	b := 1 << 62
	c := -1 << 63
	d := 'a' + 1
	e := 1.0
	f := 5 / 2.0
	g := 1e3
	h := 'a' * 2
	i := 1 << 31
	j := 1 << 63 >> 1
	k := 'x' - 'a'
	l := len("ab") + 1
	m := 3 + 0.5
	n := 255
	return a, b, c, d, e, f, g, h, i, j, k, l, m, uint8(n)
}

type cI8 int8

func constantsAtDefinedKinds() (cI8, cI8, cI8, cI8) {
	const k cI8 = -128 // a constant `k - 1` or `k / -1` is a constant overflow gc rejects (the negative rows)
	var x cI8 = 127
	var y cI8 = k
	return k, x + 1, y - 1, y / -1
}

func main() {
	typedConstantExtremes()
	constantFolding()
	constantsIntoFloats()
	floatLiteralRationals()
	floatConstantCountAndIndex()
	untypedDefaults()
	constantsAtDefinedKinds()
}
