// R4 probe: the FMA-discriminating shape. With per-op rounding
// (no fusion), x*y rounds to 1+2^-26 and x*y+z == 0. A fused
// single-rounding FMA yields the exact residue 2^-54 != 0.
// math.FMA computes the fused value for contrast (out of the
// machine's scope; it witnesses what fusion WOULD give).
package main

import "math"

func main() {
	e27 := math.Ldexp(1, -27) // 2^-27
	e26 := math.Ldexp(1, -26) // 2^-26
	x := 1.0 + e27
	y := 1.0 + e27
	z := -(1.0 + e26)
	unfusedOrFused := x*y + z
	println("x*y + z          =", unfusedOrFused)
	println("math.FMA(x,y,z)  =", math.FMA(x, y, z))
	println("2^-54            =", math.Ldexp(1, -54))
	println("fused?           =", unfusedOrFused != 0)
}
