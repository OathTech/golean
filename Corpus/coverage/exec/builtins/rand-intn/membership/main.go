package main

import "math/rand"

// The `[0, n)` DRAW as ONE choice-tape pick (window unit 5b, 2026-09-30;
// GoCore Stmt.randIntn / ChoiceSite.intn — the envelope statement is that
// constructor's docstring; design docs/2026-09-30_intn-pick-design.md).
// Membership row: the machine ENUMERATES exactly {0,1,2,3,4} at bound 5 and
// every `go run` sample lands inside — the admitted set IS the callee's
// documented range (math/rand.Intn: "a non-negative pseudo-random number in
// the half-open interval [0,n)", deps/go/src/math/rand/rand.go:176 @ go1.26.5).
func drawFive() int {
	return rand.Intn(5)
}

func main() {
	println(drawFive())
}
