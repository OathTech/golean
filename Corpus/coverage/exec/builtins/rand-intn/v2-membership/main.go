package main

// The explicit alias was first a workaround for the ORACLE HARNESS, whose
// `importName` assumed an import binds `path.Base(path)` — `v2` here — and
// pruned it as unused (handoff docs/2026-09-30_intn-pick-handoff.md §4a).
// Fixed for train r58 (audit F4: goimports' assumed-name rule); the alias
// stays so the ALIASED spelling is covered (v2-membership-unaliased: bare).
import rand "math/rand/v2"

// The same site through the v2 callee (math/rand/v2.IntN, v2/rand.go:189 @
// go1.26.5 — "a non-negative pseudo-random number in the half-open interval
// [0,n)"): bound 3, admitted set {0,1,2}; both callees are ONE machine op,
// the callee tag choosing only the guard's text.
func drawThree() int {
	return rand.IntN(3)
}

func main() {
	println(drawThree())
}
