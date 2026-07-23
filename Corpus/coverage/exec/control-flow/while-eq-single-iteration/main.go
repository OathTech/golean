package main

// Arc E rung B1 guardrail (docs/2026-07-22_arc-e-while-invariant.md §3):
// the exact witness shape for the while-invariant WP law — an
// eq-conditioned loop that runs exactly one iteration. Pins the target
// behavior before the law exists (guardrails-first).
func whileEqSingleIteration() int {
	x := 0
	for x == 0 {
		x = x + 1
	}
	return x
}

func main() {
	whileEqSingleIteration()
}
