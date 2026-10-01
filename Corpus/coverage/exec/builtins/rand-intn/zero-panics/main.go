package main

import "math/rand"

// The n <= 0 CONTROL, exact text: math/rand.Intn's own guard
// `if n <= 0 { panic("invalid argument to Intn") }` (deps/go/src/math/rand/
// rand.go:179-181 @ go1.26.5) — emitted by the lowering AHEAD of the draw as
// the language-level panic(string) it is (design D2), so the abort line is
// `panic: invalid argument to Intn` on both oracles and no pick is drawn.
func drawZero() int {
	return rand.Intn(0)
}

func main() {
	println(drawZero())
}
