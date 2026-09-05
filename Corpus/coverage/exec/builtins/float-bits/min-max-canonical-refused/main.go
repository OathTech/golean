package main

import "math"

// DESIGNED RED (A1; BUG-094; R7): min/max over a machine-PRODUCED NaN. gc
// reports 0xFFF8… | 0x4004… = 0xFFFC000000000000; the machine's default NaN
// carries the opposite sign, so an OR would report a sign-wrong pattern the
// *bits guard could not recognize — floatMinMaxBits returns the default NaN
// whenever either operand is one, and the guard refuses it by name.
func minMaxCanonicalRefused() uint64 {
	z := 0.0
	n := z / z
	return math.Float64bits(min(n, 2.5))
}
