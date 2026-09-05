package main

import "math"

// gc/amd64's float min/max lowering (AMD64.rules: t1 = MINSD x y; t2 = MINSD
// t1 x; POR t1 t2; max = -min(-x,-y)) ORs the operands' bits when one is a
// NaN — the payload gc REPORTS through Float64bits is the OR, not the NaN
// operand (audit fix round A1, 2026-09-05: the first cut returned the
// operand and was wrong). Transcribed in Ops.lean floatMinMaxBits; pinned
// here over frombits payloads in both operand orders, both widths, the
// ±0 tie cases and a NaN/NaN pair.
func minMaxPayload() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	n := math.Float64frombits(0x7FF8000000000001)
	s := math.Float64frombits(0x7FF0000000000001) // signalling
	z := 0.0
	nz := -z
	return math.Float64bits(min(n, 2.5)), math.Float64bits(min(2.5, n)),
		math.Float64bits(max(n, -2.5)), math.Float64bits(max(-2.5, n)),
		math.Float64bits(min(n, s)), math.Float64bits(max(s, n)),
		math.Float64bits(min(z, nz)), math.Float64bits(max(nz, z))
}

func minMaxPayload32() (uint32, uint32, uint32, uint32) {
	n := math.Float32frombits(0x7FC00001)
	var f float32 = 1.5
	return math.Float32bits(min(n, f)), math.Float32bits(min(f, n)),
		math.Float32bits(max(n, -f)), math.Float32bits(max(-f, n))
}
