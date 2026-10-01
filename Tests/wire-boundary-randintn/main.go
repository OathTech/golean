package main

// The `rand-intn` wire-boundary fixture (window unit 5b): `probe` answers
// 42 through the `[0, n)` draw at bound 1 — the one member is 0, a bound-1
// consult that pops nothing, so the positive control is deterministic on
// every tape. The controls mutate this wire's BYTES (a forged callee tag, a
// non-int result type, an absent resultTypes vector, two targets) and must
// refuse through the real CLI naming the cause (GoLean/NativeToIR.lean
// `asRandIntnOp?` / the assignment consumer).

import "math/rand"

func probe() int {
	v := rand.Intn(1)
	return v + 42
}

func main() {
	println(probe())
}
