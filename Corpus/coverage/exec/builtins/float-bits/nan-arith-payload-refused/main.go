package main

import "math"

// DESIGNED RED (BUG-094; R7): arithmetic on a payload-carrying NaN. gc/amd64
// propagates the operand's payload (0x7FF8000000000001 * 2 keeps the
// payload); the machine's softfloat returns the canonical NaN, which the
// primitive refuses by name. The over-refusal twin (the canonical pattern
// entered through frombits and merely round-tripped) is the second row.
func nanArithPayloadRefused() uint64 {
	n := math.Float64frombits(0x7FF8000000000001)
	return math.Float64bits(n * 2)
}

func canonicalRoundtripRefused() uint64 {
	return math.Float64bits(math.Float64frombits(0x7FF8000000000000))
}
