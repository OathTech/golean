package main

// The explicit alias is for the ORACLE HARNESS: tools/coverageharness/main.go
// `importName` assumes an import binds `path.Base(path)` — `v2` here — and
// prunes the import as unused (the Go build then fails `undefined: rand`).
// Go's rule is the imported package clause (`rand`); the alias states it.
// Recorded as an apparatus finding in docs/2026-09-30_intn-pick-handoff.md.
import rand "math/rand/v2"

// The n <= 0 CONTROL for the v2 callee, exact text: math/rand/v2.IntN's guard
// `if n <= 0 { panic("invalid argument to IntN") }` (v2/rand.go:192-193 @
// go1.26.5) — the callee tag selects THIS text; a negative bound takes the
// same path as zero.
func drawNegative() int {
	return rand.IntN(-3)
}

func main() {
	println(drawNegative())
}
