package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md; the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Group A4: the float observation is a bit pattern (`bits`) with its kind; NaN is canonicalized on both sides,
// signed zero is not; every special value is produced at RUN TIME from a variable.

type F64 float64
type F32 float32

var zero = 0.0
var one = 1.0
var zero32 float32 = 0
var one32 float32 = 1

func f64SignedZeros() (float64, float64, float64) { return zero, -zero, 1 / (1 / -zero) }
func f64NaNCanonical() (float64, float64, float64) {
	n := zero / zero
	return n, -n, n * 2
}
func f64Infinities() (float64, float64, float64) {
	return one / zero, -one / zero, (one / zero) - (one / zero)
}
func f64DenormalAndMax() (float64, float64, float64) {
	d := 5e-324
	m := 1.7976931348623157e308
	return d * one, m * one, d / 2
}
func f32SignedZeros() (float32, float32) { return zero32, -zero32 }
func f32NaNCanonical() (float32, float32) {
	n := zero32 / zero32
	return n, -n
}
func f32InfinitiesDenormal() (float32, float32, float32, float32) {
	var d float32 = 1e-45
	var m float32 = 3.4028235e38
	return one32 / zero32, -one32 / zero32, d * one32, m * one32
}
func definedFloatKinds() (F64, F32, [2]F32) {
	return F64(1.5) * F64(one), F32(-2.5) * F32(one32), [2]F32{0.1, 0.2}
}

func main() {
	f64SignedZeros()
	f64NaNCanonical()
	f64Infinities()
	f64DenormalAndMax()
	f32SignedZeros()
	f32NaNCanonical()
	f32InfinitiesDenormal()
	definedFloatKinds()
}
