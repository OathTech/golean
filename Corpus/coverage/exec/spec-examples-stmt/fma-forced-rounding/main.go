package main

// spec#Floating_point_operators block
// Floating_point_operators-1-72956e18: "An explicit floating-point
// type conversion rounds to the precision of the target type,
// preventing fusion that would discard that rounding." The block's
// second half lists the forms where FMA is DISALLOWED for computing r,
// "because it would omit rounding of x*y":
//     r = float64(x*y) + z
//     r = z; r += float64(x*y)
//     t = float64(x*y); r = t + z
// These are the FORCED (no-latitude) lines: every conforming
// implementation must round x*y to float64 before the addition, so all
// three forms produce the identical value bit-for-bit, with values
// (x = 3e, y = e/3, z = -e, e = 1) chosen so a fused x*y + z would
// differ (x*y is inexact). The block's first half (FMA ALLOWED:
// r = x*y + z etc.) is implementation LATITUDE, deliberately NOT
// pinned here — the gc-pin tripwire for that envelope already exists
// at floats/fma-shape (floats design note 2026-08-04 §3.1).
// The int parameter defeats compile-time constant folding, as in
// fma-shape.

func fmaForcedConvAdd(e int) float64 {
	x := float64(e) * 3
	y := float64(e) / 3
	z := -float64(e)
	var r float64
	r = float64(x*y) + z
	return r
}

func fmaForcedPlusAssign(e int) float64 {
	x := float64(e) * 3
	y := float64(e) / 3
	z := -float64(e)
	var r float64
	r = z
	r += float64(x * y)
	return r
}

func fmaForcedTempConv(e int) float64 {
	x := float64(e) * 3
	y := float64(e) / 3
	z := -float64(e)
	var t, r float64
	t = float64(x * y)
	r = t + z
	return r
}

// The spec forces all three disallowed forms to agree exactly.
func fmaForcedFormsAgree(e int) bool {
	a := fmaForcedConvAdd(e)
	b := fmaForcedPlusAssign(e)
	c := fmaForcedTempConv(e)
	return a == b && b == c
}

func main() {
	fmaForcedFormsAgree(1)
}
