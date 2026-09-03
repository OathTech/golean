// noodler probes — IEEE-754 edges under Go's per-operation rounding
// (spec#Floating-point_operators, spec#Numeric_types; latitude R4/R5/R7).
package main

// float32 addition rounds per operation: 2^24 + 1 == 2^24.
func float32PerOpRounding() (bool, bool, float32, float64) {
	var a float32 = 16777216
	one := float32(1)
	return a+one == a, (a+one)+one == a, a + one + one + one, float64(a) + 1
}

// Infinities from division by a zero VARIABLE (no panic: R5).
func infinityArithmetic() (bool, bool, bool, bool, bool) {
	zero := 0.0
	inf := 1 / zero
	ninf := -1 / zero
	return inf > 1e308, ninf < -1e308, inf-inf != inf-inf, inf*zero != inf*zero, inf+1 == inf
}

// NaN comparisons are all false except !=.
func nanComparisons() (bool, bool, bool, bool, bool, bool) {
	zero := 0.0
	nan := zero / zero
	return nan == nan, nan != nan, nan < 1, nan > 1, nan <= nan, nan >= 1
}

// Signed zero: equal to +0, but distinguishable through division and
// sign propagation.
func signedZeroBehaviour() (bool, bool, bool, bool) {
	zero := 0.0
	negZero := -zero
	one := 1.0
	return negZero == zero, one/negZero < 0, one/(negZero+zero) > 0, one/(zero*-1) < 0
}

// Denormals: the smallest positive float64 halves to zero.
func denormalEdges() (bool, bool, bool) {
	tiny := 5e-324
	two := 2.0
	x := 1e-310
	return tiny/two == 0, tiny*0.5 == 0, x*x == 0
}

// float32 overflow to +Inf at runtime and by conversion from float64.
func float32Overflow() (bool, bool, bool) {
	var big float32 = 3e38
	ten := float32(10)
	d := 1e39
	f := float32(d)
	return big*ten > 3e38, f > 3e38, -f < -3e38
}

// float -> int truncation for in-range values at width boundaries.
func floatToIntBoundaries() (int64, int32, int8, int8, uint64) {
	a := 1e18
	b := -2147483648.0
	c := 127.9
	d := -128.9
	e := 9223372036854775808.0
	return int64(a), int32(b), int8(c), int8(d), uint64(e)
}

// Repeated addition of 0.1 does not reach 1.0 in either precision.
func tenthsAccumulate() (bool, bool, bool) {
	s64 := 0.0
	var s32 float32
	for i := 0; i < 10; i++ {
		s64 += 0.1
		s32 += 0.1
	}
	return s64 == 1.0, s32 == 1.0, float64(s32) == float64(float32(1.0))
}

// Compound float assignments and IncDec.
func floatCompoundOps() (float64, float32) {
	f := 3.0
	f *= 2
	f /= 4
	f -= 1
	f++
	var g float32 = 1
	g /= 3
	g *= 3
	return f, g
}

// float32 division then multiplication may or may not round-trip.
func float32DivMulRoundTrip() (bool, bool) {
	var one, three float32 = 1, 3
	var seven float32 = 7
	return one/three*three == one, one/seven*seven == one
}

// Widening a float32 then comparing with the float64 constant.
func widenFloat32Compare() (bool, bool) {
	var f float32 = 0.1
	var g float32 = 0.5
	return float64(f) == 0.1, float64(g) == 0.5
}

// NaN survives float32 <-> float64 conversion.
func nanConversions() (bool, bool) {
	zero := 0.0
	nan := zero / zero
	f := float32(nan)
	back := float64(f)
	return f != f, back != back
}

// Integer-valued floats compare equal to integer conversions exactly
// up to 2^53; beyond, the conversion rounds.
func floatIntegerBoundary() (bool, bool, float64) {
	var i int64 = 1<<53 - 1
	var j int64 = 1<<53 + 1
	return float64(i) == 9007199254740991, float64(j) == 9007199254740992, float64(j) - float64(i)
}

// Subtraction of nearly-equal values loses precision (catastrophic
// cancellation), deterministic under per-op rounding.
func cancellation() (float64, bool) {
	a := 1.0000001
	b := 1.0
	d := a - b
	return d, d == 1e-7
}

// Float in a map key and a switch after arithmetic that yields -0.
func negativeZeroKeyAfterArithmetic() (int, int) {
	zero := 0.0
	m := map[float64]int{}
	m[zero] = 1
	m[zero*-1] = 2
	r := 0
	switch zero * -1 {
	case 0:
		r = 1
	default:
		r = 2
	}
	return len(m)*10 + m[0], r
}

func main() {}
