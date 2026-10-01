package main

// The explicit alias was first a workaround for the ORACLE HARNESS, whose
// `importName` assumed an import binds `path.Base(path)` — `v2` here — and
// pruned it as unused (handoff docs/2026-09-30_intn-pick-handoff.md §4a).
// Fixed for train r58 (audit F4: goimports' assumed-name rule); the alias
// stays so the ALIASED spelling is covered (v2-membership-unaliased: bare).
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
