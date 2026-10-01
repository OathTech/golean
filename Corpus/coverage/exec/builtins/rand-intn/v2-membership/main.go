package main

// The explicit alias is for the ORACLE HARNESS: tools/coverageharness/main.go
// `importName` assumes an import binds `path.Base(path)` — `v2` here — and
// prunes the import as unused (the Go build then fails `undefined: rand`).
// Go's rule is the imported package clause (`rand`); the alias states it.
// Recorded as an apparatus finding in docs/2026-09-30_intn-pick-handoff.md.
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
