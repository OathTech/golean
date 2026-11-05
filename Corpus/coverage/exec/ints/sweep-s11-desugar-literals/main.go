package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group Q4 (BUG-042/043/174's positions): an
// untyped constant in arithmetic at a DEFINED integer type of every width at the kind's extremes
// (the literal takes the underlying kind — emitConstValue), the IncDec and compound desugars'
// synthetic literals at defined kinds, `range` over an integer of every kind at its extreme with
// the loop variable in arithmetic (decodeRange's $ridx/$rlen at the operand's kind), range over a
// typed constant, the loop variable modified in the body (the count unchanged), a method on the
// loop variable, and map compounds at every value kind (emitMapCompound's synthetic literal).

import "math"

type c8 int8
type c16 int16
type c32 int32
type c64 int64
type cI int
type u8 uint8
type u16 uint16
type u32 uint32
type u64 uint64
type uP uintptr
type cF32 float32
type cnt int8

func (c cnt) dbl() cnt { return c * 2 }

func definedLiteralInt8() (c8, c8, c8, c8, c8, c8, c8, c8, c8, c8) {
	var c c8 = 127
	d := c
	d += 1
	e := c
	e++
	return c + 1, c * 2, c - 1, c / 2, c % 3, c << 1, c | 1, c &^ 1, d, e
}

func definedLiteralInt16() (c16, c16, c16, c16, c16, c16) {
	var c c16 = -32768
	d := c
	d -= 1
	e := c
	e--
	return c - 1, c * 2, c / -1, c >> 15, c ^ -1, d + e
}

func definedLiteralInt32() (c32, c32, c32, c32, c32, c32) {
	var c c32 = 2147483647
	d := c
	d *= 2
	e := c
	e++
	return c + 1, c * 2, c + 1 - 1, c << 1, c % 1000, d - e
}

func definedLiteralInt64() (c64, c64, c64, c64, c64, c64) {
	var c c64 = -9223372036854775808
	d := c
	d /= -1
	e := c
	e--
	return c - 1, c * 2, c / -1, c % -1, c >> 63, d + e
}

func definedLiteralInt() (cI, cI, cI, cI) {
	var c cI = 9223372036854775807
	d := c
	d += 1
	return c + 1, c * 2, c << 1, d
}

func definedLiteralUnsigned() (u8, u16, u32, u64, uint64, u8, u16, u32, u64, uint64) {
	var a u8 = 255
	var b u16 = 65535
	var c u32 = 4294967295
	var d u64 = 18446744073709551615
	var e uP = 18446744073709551615
	a2 := a
	a2 += 1
	b2 := b
	b2 *= 2
	c2 := c
	c2++
	d2 := d
	d2 <<= 1
	e2 := e
	e2 += 2
	return a + 1, b * 2, c + 1, d << 1, uint64(e + 1), a2, b2, c2, d2, uint64(e2)
}

func definedLiteralFloat32() (uint32, uint32, uint32, uint32) {
	var f cF32 = 0.1
	g := f
	g += 0.2
	var h cF32 = 16777216
	h++
	var i cF32 = 1
	i /= 3
	return math.Float32bits(float32(f + 0.2)), math.Float32bits(float32(g)), math.Float32bits(float32(h)), math.Float32bits(float32(i))
}

func rangeUint8Max() (uint8, int) {
	var n uint8 = 255
	var s uint8
	count := 0
	for i := range n {
		s += i
		count++
	}
	return s, count
}

func rangeInt8Max() (int8, int) {
	var n int8 = 127
	var s int8
	count := 0
	for i := range n {
		s += i
		count++
	}
	return s, count
}

func rangeWideKinds() (uint64, uint64, int64, uint32, int16) {
	var a uint64 = 5
	var b uintptr = 4
	var c int64 = 6
	var d uint32 = 3
	var e int16 = 7
	var sa uint64
	var sb uintptr
	var sc int64
	var sd uint32
	var se int16
	for i := range a {
		sa += i << 60
	}
	for i := range b {
		sb += i << 62
	}
	for i := range c {
		sc += i * 1537228672809129301
	}
	for i := range d {
		sd += i << 31
	}
	for i := range e {
		se += i * 5000
	}
	return sa, uint64(sb), sc, sd, se
}

func rangeTypedConstants() (int8, uint16, int, int) {
	var s int8
	for i := range int8(3) {
		s += i * 50
	}
	var t uint16
	for j := range uint16(16) {
		t |= 1 << j
	}
	count := 0
	for range uint8(4) {
		count++
	}
	n := 0
	for i := range 'c' {
		n += int(i)
	}
	return s, t, count, n
}

func rangeLoopVarModified() (int, int, uint8) {
	count := 0
	sum := 0
	for i := range 5 {
		i += 10
		sum += i
		count++
	}
	var u uint8
	for i := range uint8(3) {
		i = 200
		u += i
	}
	return sum, count, u
}

func rangeDefinedMethod() (cnt, int) {
	var s cnt
	count := 0
	for i := range cnt(100) {
		s += i.dbl()
		count++
	}
	return s, count
}

func mapCompoundKinds() (uint8, int8, int8, uint32, uint64, int64, int16, uint64) {
	m1 := map[int]uint8{1: 100}
	m1[1] += 200
	m2 := map[int]int8{1: -128}
	m2[1] <<= 1
	m3 := map[int]int8{1: -128}
	m3[1] *= -1
	m4 := map[int]uint32{1: 0}
	m4[1] -= 1
	m5 := map[int]uint64{1: 1 << 63}
	m5[1] <<= 1
	m6 := map[int]int64{1: 9223372036854775807}
	m6[1] += 1
	m7 := map[string]int16{"k": -32768}
	m7["k"] /= -1
	m8 := map[int]uintptr{1: 0}
	m8[1]--
	return m1[1], m2[1], m3[1], m4[1], m5[1], m6[1], m7["k"], uint64(m8[1])
}

func mapCompoundFloat32() (uint32, uint32, uint32) {
	m := map[int]float32{1: 0.1}
	m[1] += 0.2
	m2 := map[int]float32{1: 16777216}
	m2[1] += 1
	m3 := map[int]cF32{1: 1}
	m3[1] /= 3
	return math.Float32bits(m[1]), math.Float32bits(m2[1]), math.Float32bits(float32(m3[1]))
}

func main() {
	definedLiteralInt8()
	definedLiteralInt16()
	definedLiteralInt32()
	definedLiteralInt64()
	definedLiteralInt()
	definedLiteralUnsigned()
	definedLiteralFloat32()
	rangeUint8Max()
	rangeInt8Max()
	rangeWideKinds()
	rangeTypedConstants()
	rangeLoopVarModified()
	rangeDefinedMethod()
	mapCompoundKinds()
	mapCompoundFloat32()
}
