package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group L1: a float constant too SMALL for
// the type rounds to zero (spec#Constants: "rounded to the nearest representable value" — only
// overflow is an error), and a negative one to an unsigned zero (spec: an IEEE negative zero is
// simplified to an unsigned zero at constant typing). Isolated in its own package so the cells'
// legality is decided by gc on this package alone. Site ratToFloat64's underflow arm.

import "math"

func constantUnderflow() (uint64, uint64, uint32, uint64, bool) {
	var a float64 = 1e-400
	var b float64 = -1e-400
	var c float32 = 1e-50
	const tiny = 1e-400
	var d float64 = tiny * 1e200
	return math.Float64bits(a), math.Float64bits(b), math.Float32bits(c), math.Float64bits(d), a == b
}

func main() {
	constantUnderflow()
}
