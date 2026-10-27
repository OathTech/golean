package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10 — the CONTROL for
// range/sweep-s10-zero-len-two-vars (BUG-226): a two-variable range over a
// zero-length ARRAY VALUE lowers through the emitter's array arm, which keeps
// the value variable, and runs: zero iterations, no element read. gc: 0.

func zeroLenArrayTwoVars() int {
	var a [0]int
	n := 0
	for i, v := range a {
		n += i + v + 1
	}
	return n
}

func main() {}
