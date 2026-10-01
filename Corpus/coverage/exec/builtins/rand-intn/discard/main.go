package main

import "math/rand"

// The DISCARDED-RESULT form (design D4): `rand.Intn(5)` as an expression
// statement still draws — Go's generator advances, the machine's tape is
// consulted (Stmt.randIntn with no target) — and the observable does not
// depend on the value. A strict row: 7 on every tape; the invariance re-run
// across streams is what certifies the discard.
func discard() int {
	rand.Intn(5)
	return 7
}

func main() {
	println(discard())
}
