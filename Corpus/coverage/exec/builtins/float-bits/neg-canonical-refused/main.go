package main

import "math"

// DESIGNED RED (audit fix round A1, 2026-09-05; BUG-094; R7): the NEGATION of
// a machine-produced NaN. gc: -(0/0) = 0x7FF8000000000000 (a sign flip of
// its 0xFFF8… default); the machine: 0xFFF8… (a sign flip of ITS 0x7FF8…
// default). The first cut's guard tested the canonical pattern exactly and
// REPORTED the negation — a wrong answer; the guard is sign-insensitive now
// and this row pins it red. The float32 twin sits in the same subject.
func negCanonicalRefused() uint64 {
	z := 0.0
	n := z / z
	return math.Float64bits(-n)
}

func negCanonicalRefused32() uint32 {
	var z float32 = 0
	n := z / z
	return math.Float32bits(-n)
}
