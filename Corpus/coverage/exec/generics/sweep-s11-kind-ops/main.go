package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group Q1: the shape's operations inside
// GENERIC functions over type-set constraints (~int8 | … | ~uintptr, ~float32 | ~float64),
// instantiated at each concrete kind and at defined kinds: wrap at the maximum, shifts at and
// past the width, the complement, T(x) conversions, `++`, min/max, the most negative value / -1,
// a counted loop over a T, a literal T(1) in arithmetic, a shift by a T count; over floats: the FMA shape
// (no fusion), NaN ordering, min with NaN, 1/3 at float32, T(int) rounding. The monomorphizer
// must carry the instantiated kind into every synthetic literal and width lookup.

import "math"

type Ints interface {
	~int8 | ~int16 | ~int32 | ~int64 | ~int | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~uint | ~uintptr
}

type Signed interface {
	~int8 | ~int16 | ~int32 | ~int64 | ~int
}

type Floats interface {
	~float32 | ~float64
}

type dI16 int16
type dU uintptr
type dF32 float32

func addOne[T Ints](x T) T { return x + 1 }
func shl[T Ints](x T, c uint) T { return x << c }
func shr[T Ints](x T, c uint) T { return x >> c }
func compl[T Ints](x T) T { return ^x }
func conv[T Ints](x int64) T { return T(x) }
func inc[T Ints](x T) T {
	x++
	return x
}
func minMaxG[T Ints](a, b T) (T, T) { return min(a, b), max(a, b) }
func divNeg1[T Signed](x T) T {
	var m1 T = -1
	return x / m1
}
func rangeSum[T Ints](n T) T { // `for i := range n` over a T with no core type is a gc rejection (negative row)
	var s T
	for i := T(0); i < n; i++ {
		s += i
	}
	return s
}
func litArith[T Ints](x T) T { return x*2 + T(1) }
func shiftByT[T Ints](x int, c T) int { return x << c }
func fmaShape[T Floats](x, y, z T) T { return x*y + z }
func nanLess[T Floats](a, b T) bool { return a < b }
func minNaN[T Floats](a, b T) T { return min(a, b) }
func third[T Floats]() T {
	var one T = 1
	var three T = 3
	return one / three
}
func fromInt[T Floats](x int64) T { return T(x) }

func genericWrapKinds() (int8, uint8, int64, uint64, uint64, dI16, int16, uint32) {
	var mxI8 int8 = 127
	var mxU8 uint8 = 255
	var mxI64 int64 = 9223372036854775807
	var mxU64 uint64 = 18446744073709551615
	var mxP uintptr = 18446744073709551615
	var mxD dI16 = 32767
	var mxI16 int16 = 32767
	var mxU32 uint32 = 4294967295
	return addOne(mxI8), addOne(mxU8), addOne(mxI64), addOne(mxU64), uint64(addOne(mxP)), addOne(mxD), addOne(mxI16), addOne(mxU32)
}

func genericShiftKinds() (int8, uint8, int64, uint64, int32, uint64, dI16, uint16) {
	var one8 int8 = 1
	var oneU8 uint8 = 1
	var m1 int64 = -1
	var mxU64 uint64 = 18446744073709551615
	var one32 int32 = 1
	var oneP uintptr = 1
	var neg dI16 = -32768
	var mxU16 uint16 = 65535
	return shl(one8, 7), shl(oneU8, 8), shr(m1, 64), shr(mxU64, 64), shl(one32, 1<<40), uint64(shl(oneP, 63)), shr(neg, 15), shr(mxU16, 15)
}

func genericComplConv() (int8, uint16, int8, uint8, uint64, uint64, int16, dI16) {
	var z8 int8 = 0
	var z16 uint16 = 0
	return compl(z8), compl(z16), conv[int8](-1), conv[uint8](-1), conv[uint64](-1), uint64(conv[uintptr](-1)), conv[int16](70000), conv[dI16](-40000)
}

func genericIncDecMinMax() (uint8, int64, int8, int8, uint64, uint64, uint64) {
	var mxU8 uint8 = 255
	var mxI64 int64 = 9223372036854775807
	var mn8 int8 = -128
	var mx8 int8 = 127
	var zU64 uint64 = 0
	var mxU64 uint64 = 18446744073709551615
	var mxP dU = 18446744073709551615
	a, b := minMaxG(mn8, mx8)
	c, d := minMaxG(zU64, mxU64)
	return inc(mxU8), inc(mxI64), a, b, c, d, uint64(inc(mxP))
}

func genericDivRange() (int8, int64, uint8, int8, uint64, dI16, int32) {
	var mn8 int8 = -128
	var mn64 int64 = -9223372036854775808
	var n8 uint8 = 255
	var n20 int8 = 20
	var n5 uint64 = 5
	var n100 dI16 = 100
	var mn32 int32 = -2147483648
	return divNeg1(mn8), divNeg1(mn64), rangeSum(n8), rangeSum(n20), rangeSum(n5), rangeSum(n100), divNeg1(mn32)
}

func genericLitShiftByT() (int8, uint8, int, int, int, dI16, uint64) {
	var a int8 = 100
	var b uint8 = 200
	var c uint8 = 70
	var d int8 = 3
	var e dU = 63
	var f dI16 = 16383
	var g uintptr = 1
	return litArith(a), litArith(b), shiftByT(1, c), shiftByT(1, d), shiftByT(1, e), litArith(f), uint64(shl(g, 64))
}

func genericFloats() (uint32, uint64, bool, bool, bool, uint32, uint64, uint32, uint64) {
	var e float32 = 1
	x32 := 1 + e/(1<<12)
	z32 := -(1 + e/(1<<11))
	var e64 float64 = 1
	x64 := 1 + e64/(1<<27)
	z64 := -(1 + e64/(1<<26))
	var z float32 = 0
	nan32 := z / z
	var zd float64 = 0
	nan64 := zd / zd
	var one32 float32 = 1
	var one64 float64 = 1
	m := minNaN(one64, nan64)
	var df dF32 = 0
	nanD := df / df
	md := minNaN(dF32(1), nanD)
	return math.Float32bits(fmaShape(x32, x32, z32)), math.Float64bits(fmaShape(x64, x64, z64)), nanLess(nan32, one32), nanLess(one64, nan64),
		m != m, math.Float32bits(third[float32]()), math.Float64bits(third[float64]()), math.Float32bits(fromInt[float32](16777217)),
		math.Float64bits(float64(fromInt[dF32](16777219))) ^ uint64(boolToInt(md != md))
}

func boolToInt(b bool) int {
	if b {
		return 1
	}
	return 0
}

func main() {
	genericWrapKinds()
	genericShiftKinds()
	genericComplConv()
	genericIncDecMinMax()
	genericDivRange()
	genericLitShiftByT()
	genericFloats()
}
