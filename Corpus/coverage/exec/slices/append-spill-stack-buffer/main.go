package main

// gc's realized append-spill capacity for a small BYTE append: the
// compiler stack-buffers small non-escaping appends in a 32-byte
// buffer, so cap is 32 — far above the growth formula's window
// (formula 6 for oldCap 3 -> newLen 4). Probe-verified go1.26.5:
// cap = 32. This point sat OUTSIDE the modeled envelope
// (growth + [0,8)) — the arc-final audit's F2 too-narrow finding.
// Membership, samples=1: version-tracks gc's realized point against
// the widened envelope [newLen, max(32, 2*growth)].
func appendSpillStackBuffer() int {
	b := make([]byte, 0, 3)
	b = append(b, 1, 2, 3, 4)
	return cap(b)
}
