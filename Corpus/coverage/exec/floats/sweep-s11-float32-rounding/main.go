package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group H: float32 results are rounded to
// float32 after EVERY operation (gc amd64 at GOAMD64=v1 emits no fused multiply-add: MULSS then
// ADDSS, two roundings — the fma-shape tripwire at float32), ties-to-even at the float32 maximum
// (half an ulp above max32 rounds to +Inf because max32's mantissa is odd), denormal productions,
// and the SINGLE rounding of a float64 → float32 narrowing (halfway cases, the sticky bit, the
// denormal range, overflow). Observed as bit patterns. Sites FloatBits.f64to32, fadd32/fmul32/fdiv32.

import "math"

func f32PerOpRounding() (uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32) {
	var one float32 = 1
	var two float32 = 2
	var three float32 = 3
	var tenth float32 = 0.1
	var fifth float32 = 0.2
	var big float32 = 1e30
	var ten float32 = 1e10
	var mx float32 = 3.4028234663852886e38
	return math.Float32bits(one / three), math.Float32bits(two / three), math.Float32bits(tenth + fifth),
		math.Float32bits(big * ten), math.Float32bits(mx * two), math.Float32bits(mx + mx),
		math.Float32bits(-mx * two), math.Float32bits(mx - mx)
}

func f32TiesAtMax() (uint32, uint32, uint32, uint32) {
	var mx float32 = 3.4028234663852886e38
	var halfUlp float32 = 1 << 103
	var lessThanHalf float32 = 1 << 102
	var ulp float32 = 1 << 104
	return math.Float32bits(mx + halfUlp), math.Float32bits(mx + lessThanHalf), math.Float32bits(mx + ulp),
		math.Float32bits(-mx - halfUlp)
}

func f32Denormals() (uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32) {
	var minNormal float32 = 1.1754943508222875e-38
	var two float32 = 2
	var three float32 = 3
	tiny := math.Float32frombits(1)
	maxSub := math.Float32frombits(0x007FFFFF)
	return math.Float32bits(minNormal / two), math.Float32bits(tiny / two), math.Float32bits(three * tiny / two),
		math.Float32bits(maxSub + tiny), math.Float32bits(minNormal - tiny), math.Float32bits(tiny * two),
		math.Float32bits(tiny + tiny), math.Float32bits(maxSub * two)
}

func f32FMAShape(e int) (uint32, uint32, uint32, uint32) {
	x := 1 + float32(e)/(1<<12)
	y := x
	z := -(1 + float32(e)/(1<<11))
	r := x*y + z
	s := x*y - (-z)
	t := x * y
	var acc float32 = x
	acc *= y
	acc += z
	return math.Float32bits(r), math.Float32bits(s), math.Float32bits(t), math.Float32bits(acc)
}

func f32Cancellation() (uint32, uint32, uint32, uint32) {
	var a float32 = 1.0000001
	var b float32 = 1
	var c float32 = 16777216
	var d float32 = 1.1
	d *= 3
	var e float32 = 0.3
	e -= 0.1
	return math.Float32bits(a - b), math.Float32bits(c + 1 - c), math.Float32bits(d), math.Float32bits(e)
}

func narrowTies() (uint32, uint32, uint32, uint32, uint32) {
	a := math.Float64frombits(0x3FF0000010000000) // 1 + 2^-24: halfway, ties to even (down)
	b := math.Float64frombits(0x3FF0000030000000) // 1 + 3·2^-24: halfway, ties to even (up)
	c := math.Float64frombits(0x3FF0000010000001) // halfway plus a sticky bit: up
	d := math.Float64frombits(0x3FF000000FFFFFFF) // just below halfway: down
	e := math.Float64frombits(0x3FF0000020000000) // 1 + 2^-23: exact
	return math.Float32bits(float32(a)), math.Float32bits(float32(b)), math.Float32bits(float32(c)),
		math.Float32bits(float32(d)), math.Float32bits(float32(e))
}

func narrowDenormals() (uint32, uint32, uint32, uint32, uint32, uint32) {
	a := math.Float64frombits(0x3690000000000000) // 2^-150: halfway between 0 and the smallest float32 denormal
	b := math.Float64frombits(0x3690000000000004) // 2^-150 + 2^-200: rounds up to 0x00000001
	c := math.Float64frombits(0x36A8000000000000) // 1.5 · 2^-149: ties to even → 0x00000002
	var d float64 = 1e-40
	e := math.Float64frombits(0x3698000000000000) // 0.75 · 2^-149: rounds up to 0x00000001
	f := math.Float64frombits(0x380FFFFFFFFFFFFF) // just below the smallest float32 normal
	return math.Float32bits(float32(a)), math.Float32bits(float32(b)), math.Float32bits(float32(c)),
		math.Float32bits(float32(d)), math.Float32bits(float32(e)), math.Float32bits(float32(f))
}

func narrowOverflow() (uint32, uint32, uint32, uint32, uint32, uint32) {
	a := math.Float64frombits(0x47EFFFFFF0000000) // max32 + half an ulp: ties to even → +Inf
	b := math.Float64frombits(0x47EFFFFFE8000000) // max32 + a quarter ulp: max32
	var c float64 = 3.5e38
	d := math.Float64frombits(0x47EFFFFFEFFFFFFF) // just below the halfway: max32
	e := math.Float64frombits(0xC7EFFFFFF0000000) // -(max32 + half an ulp): -Inf
	var f float64 = 1.7976931348623157e308
	return math.Float32bits(float32(a)), math.Float32bits(float32(b)), math.Float32bits(float32(c)),
		math.Float32bits(float32(d)), math.Float32bits(float32(e)), math.Float32bits(float32(f))
}

func narrowAndWidenSpecials() (uint32, uint32, uint32, uint32, uint64, uint64, uint64, uint64) {
	z := 0.0
	nz := -z
	var one float64 = 1
	inf := one / z
	var exactMax float64 = 3.4028234663852886e38
	var nz32 float32 = 0
	nz32 = -nz32
	sub32 := math.Float32frombits(1)
	var max32 float32 = 3.4028234663852886e38
	var inf32 float32 = max32 * 2
	return math.Float32bits(float32(inf)), math.Float32bits(float32(-inf)), math.Float32bits(float32(nz)),
		math.Float32bits(float32(exactMax)), math.Float64bits(float64(sub32)), math.Float64bits(float64(nz32)),
		math.Float64bits(float64(max32)), math.Float64bits(float64(inf32))
}

func main() {
	f32PerOpRounding()
	f32TiesAtMax()
	f32Denormals()
	f32FMAShape(1)
	f32Cancellation()
	narrowTies()
	narrowDenormals()
	narrowOverflow()
	narrowAndWidenSpecials()
}
