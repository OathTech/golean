package main

import "math"

// The float-bits PRIMITIVE (stdlib slice 3): Float64bits ∘ Float64frombits
// is the identity on EVERY bit pattern the audit condition names — the
// math.NaN payload (0x7FF8000000000001), a signalling NaN, a negative
// quiet NaN, ±0, ±Inf, the subnormal minimum, the finite maximum, 1.0.
// The patterns travel through the machine's representation untouched.
func roundtripPayloads() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	ps := [10]uint64{
		0x7FF8000000000001, // math.NaN()'s payload (internal/strconv deps.go:29 builds nan() from it)
		0x7FF0000000000001, // signalling NaN
		0xFFF8000000000000, // negative quiet NaN (x86's "real indefinite")
		0x8000000000000000, // -0
		0x0000000000000000, // +0
		0x7FF0000000000000, // +Inf
		0xFFF0000000000000, // -Inf
		0x0000000000000001, // smallest subnormal
		0x7FEFFFFFFFFFFFFF, // largest finite
		0x3FF0000000000000, // 1.0
	}
	var r [10]uint64
	for i, p := range ps {
		r[i] = math.Float64bits(math.Float64frombits(p))
		println(r[i])
	}
	return r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9]
}
