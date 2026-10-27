package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: floating-point
// division by a run-time zero raises NO panic in gc (spec#Arithmetic_operators:
// implementation-specific; gc realizes IEEE 754 — floats/division-specials pins
// float64 with a local zero). Here float32, and the compound form, with the
// zero arriving as the entry argument.

func float32DivZero(z int) int {
	x := float32(1.5)
	y := float32(z)
	q := x / y
	n := -x / y
	s := y / y
	score := 0
	if q > 1e30 {
		score += 1
	}
	if n < -1e30 {
		score += 10
	}
	if s != s {
		score += 100
	}
	return score
}

func float64DivAssignZero(z int) int {
	x := 2.0
	y := float64(z)
	x /= y
	if x > 1e300 {
		return 1
	}
	return 0
}

func main() {}
