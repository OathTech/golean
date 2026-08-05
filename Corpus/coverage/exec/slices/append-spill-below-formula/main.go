package main

// gc's realized append-spill capacity BELOW the growth formula: for a
// 16-byte element (string) appended twice to a nil slice, gc allocates
// exactly newLen (cap 2), under the formula's max(4, newLen) = 4.
// Probe-verified go1.26.5. The spec's only floor is "sufficiently
// large" (>= newLen), so the envelope's lower end must be newLen, not
// the formula. Membership, samples=1 (arc-final audit F2).
func appendSpillBelowFormula() int {
	var s []string
	s = append(s, "a", "b")
	return cap(s)*10 + len(s[0]) + len(s[1])
}
