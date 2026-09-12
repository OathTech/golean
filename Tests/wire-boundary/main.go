package main

// Fixture for scripts/check-wire-boundary (BUG-110; whole-project review
// 2026-09-11 F3 = 2026-09-05 gate audit F9): the review's discard-call
// probe. `_ = val()` lowers to a call whose blank target is typed by the
// call node's `resultTypes` vector — the vector the decoder used to
// reconstruct as `int` when a mutated wire omitted it. The gate lowers
// this file with the real frontend, mutates the wire's BYTES, and drives
// each mutant through the real CLI (`golean native-json-run`).
func val() int { return 7 }

func probe() int {
	_ = val()
	return 42
}

func main() { println(probe()) }
