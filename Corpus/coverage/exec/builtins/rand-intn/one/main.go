package main

import "math/rand"

// The n = 1 CONTROL: `[0, 1)` has the one member 0 — a bound-1 consult that
// pops nothing under the uniform rule (G-U), so this is a strict row: the
// value is 0 on every tape, and the choice trace records no pick here.
func drawOne() int {
	return rand.Intn(1)
}

func main() {
	println(drawOne())
}
