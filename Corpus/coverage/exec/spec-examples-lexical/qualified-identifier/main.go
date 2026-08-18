// spec#Qualified_identifiers block Qualified_identifiers-2-cfbc14aa
// The spec's example qualified identifier: math.Sin denotes the Sin
// function in package math. Pins the form both as a direct call and
// as a first-class function value, with the exact value Sin(0) == 0.
// NOTE: stdlib "math" is not yet in the frontend's supported imports —
// expected to surface as a visible frontend-blocked red, never a
// false pass (guardrail-first).
package main

import "math"

func qualifiedIdentifier() int {
	f := math.Sin // denotes the Sin function in package math
	score := 0
	if math.Sin(0) == 0 {
		score += 1
	}
	if f(0) == 0 {
		score += 2
	}
	return score
}

func main() {
	qualifiedIdentifier()
}
