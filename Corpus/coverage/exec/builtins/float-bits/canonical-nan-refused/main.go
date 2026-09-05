package main

import "math"

// DESIGNED RED (stdlib slice 3; BUGS.md BUG-094; latitude R7): the bits of
// a NaN the MACHINE PRODUCES (0/0 at run time). gc/amd64 realizes the
// hardware pattern 0xFFF8000000000000 (SSE "real indefinite"); the
// machine narrows every produced NaN to 0x7FF8000000000000 (softfloat64.go's
// own rule). float-bits REFUSES the canonical pattern by name rather than
// reporting the narrowing as an answer — R7's re-envelope obligation.
func canonicalNaNRefused() uint64 {
	z := 0.0
	n := z / z
	return math.Float64bits(n)
}
