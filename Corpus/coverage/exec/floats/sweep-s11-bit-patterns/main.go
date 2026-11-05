package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group I: the BIT PATTERNS of float results —
// signed zeros from every production that yields one (IEEE 754 §6.3: the sign of a zero sum is +
// unless both operands are -0, a product's sign is the XOR, x - x is +0), denormal arithmetic at
// the bottom of the binary64 range (gradual underflow, ties to even at the smallest denormal),
// infinities from overflow and division (the rounding rule at the maximum: half an ulp above max64
// rounds to +Inf), the extreme literals, the math package constants, and a payload NaN carried
// unchanged through every value route (no arithmetic touches it, so the payload is bit-exact on
// both sides — BUG-094's refusal is only for a machine-PRODUCED NaN). Observed by math.Float64bits.

import "math"

func signedZeroProductions() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	z := 0.0
	nz := -z
	var one float64 = 1
	var m1 float64 = -1
	inf := one / z
	return math.Float64bits(-z), math.Float64bits(z * m1), math.Float64bits(m1 / inf), math.Float64bits(z - z),
		math.Float64bits(nz + nz), math.Float64bits(nz + z), math.Float64bits(nz - z), math.Float64bits(z - nz),
		math.Float64bits(nz * nz), math.Float64bits(nz * z), math.Float64bits(one - one), math.Float64bits(nz / one)
}

func signedZeroConversions() (uint64, uint64, uint32, uint64, int, uint64, bool, bool, uint32, uint32) {
	z := 0.0
	nz := -z
	var m1 float64 = -1
	var nz32 float32 = 0
	nz32 = -nz32
	var z32 float32 = 0
	var m132 float32 = -1
	return math.Float64bits(z / m1), math.Float64bits(nz / m1), math.Float32bits(float32(nz)), math.Float64bits(float64(nz32)),
		int(nz), math.Float64bits(float64(int(nz))), nz == z, nz < z, math.Float32bits(z32 * m132), math.Float32bits(nz32 + z32)
}

func denormalArith() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	sub := math.Float64frombits(1)
	maxSub := math.Float64frombits(0x000FFFFFFFFFFFFF)
	minNormal := math.Float64frombits(0x0010000000000000)
	var two float64 = 2
	var three float64 = 3
	var big float64 = 4503599627370496 // 2^52
	return math.Float64bits(sub + sub), math.Float64bits(maxSub + sub), math.Float64bits(minNormal - sub),
		math.Float64bits(sub * two), math.Float64bits(sub / two), math.Float64bits(three * sub / two),
		math.Float64bits(minNormal / two), math.Float64bits(sub * big), math.Float64bits(maxSub * two),
		math.Float64bits(sub / sub)
}

func denormalCompareAndConvert() (bool, bool, bool, uint32, uint64, int, uint64, uint64, uint64, uint64) {
	sub := math.Float64frombits(1)
	maxSub := math.Float64frombits(0x000FFFFFFFFFFFFF)
	minNormal := math.Float64frombits(0x0010000000000000)
	sub32 := math.Float32frombits(1)
	var ten float64 = 10
	const folded = 5e-324 * 10
	return sub > 0, sub < minNormal, sub == 0, math.Float32bits(float32(sub)), math.Float64bits(float64(sub32)),
		int(maxSub), math.Float64bits(5e-324), math.Float64bits(2.2250738585072014e-308), math.Float64bits(1e-310),
		math.Float64bits(sub*ten) ^ math.Float64bits(folded)
}

func infinityProductions() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	z := 0.0
	var one float64 = 1
	var m1 float64 = -1
	var mx float64 = 1.7976931348623157e308
	var two float64 = 2
	inf := one / z
	return math.Float64bits(one / z), math.Float64bits(m1 / z), math.Float64bits(mx * two), math.Float64bits(mx + mx),
		math.Float64bits(-mx * two), math.Float64bits(inf + one), math.Float64bits(inf * m1), math.Float64bits(inf - one),
		math.Float64bits(one / inf), math.Float64bits(m1 / inf)
}

func infinityRounding() (uint64, uint64, uint64, uint64, uint32, uint64, bool, bool, bool, bool, bool, bool) {
	z := 0.0
	var one float64 = 1
	var two float64 = 2
	var mx float64 = 1.7976931348623157e308
	halfUlp := math.Float64frombits(0x7C90000000000000)      // 2^970 (an untyped 1 << 970 exceeds gc's 512-bit constant limit)
	lessThanHalf := math.Float64frombits(0x7C80000000000000) // 2^969
	inf := one / z
	var max32 float32 = 3.4028234663852886e38
	inf32 := max32 * 2
	return math.Float64bits(mx + halfUlp), math.Float64bits(mx + lessThanHalf), math.Float64bits(-mx - halfUlp),
		math.Float64bits(inf / two), math.Float32bits(float32(inf)), math.Float64bits(float64(inf32)),
		inf > mx, -inf < -mx, inf == inf, (inf - inf) != (inf - inf), (inf * z) != (inf * z), (inf / inf) != (inf / inf)
}

func extremeLiterals() (uint64, uint64, uint64, uint32, uint32, uint32, uint64, uint64) {
	return math.Float64bits(1.7976931348623157e308), math.Float64bits(2.2250738585072014e-308), math.Float64bits(4.9406564584124654e-324),
		math.Float32bits(3.4028234663852886e38), math.Float32bits(1.1754943508222875e-38), math.Float32bits(1.401298464324817e-45),
		math.Float64bits(1e23), math.Float64bits(9007199254740993.0)
}

func mathConstants() (uint64, uint64, uint32, int64, int64, uint64, int8, uint64, uint32) {
	return math.Float64bits(math.MaxFloat64), math.Float64bits(math.SmallestNonzeroFloat64), math.Float32bits(math.MaxFloat32),
		math.MaxInt64, math.MinInt64, math.MaxUint64, math.MaxInt8, math.Float64bits(math.Pi), math.Float32bits(math.Pi)
}

type carrier struct{ f float64 }

func identity(x float64) float64 { return x }

func nanPayloadRoundTrips() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint32) {
	n := math.Float64frombits(0x7FF0000000000001)
	q := math.Float64frombits(0x7FF800000000BEEF)
	v := q
	b := carrier{f: q}
	s := []float64{n}
	m := map[int]float64{1: q}
	ch := make(chan float64, 1)
	ch <- n
	r := <-ch
	var i any = q
	w := i.(float64)
	q32 := math.Float32frombits(0x7FC0BEEF)
	arr := [1]float32{q32}
	return math.Float64bits(v), math.Float64bits(b.f), math.Float64bits(s[0]), math.Float64bits(m[1]), math.Float64bits(r),
		math.Float64bits(w), math.Float64bits(identity(n)), math.Float64bits(-(-q)), math.Float32bits(arr[0])
}

func main() {
	signedZeroProductions()
	signedZeroConversions()
	denormalArith()
	denormalCompareAndConvert()
	infinityProductions()
	infinityRounding()
	extremeLiterals()
	mathConstants()
	nanPayloadRoundTrips()
}
