package main

import "fmt"

// Per-declaration quarantine for METHODS (H-3): one method the frontend
// cannot lower (`fmt.Sprintf` is not modeled) must not block the export of
// the methods, functions, and types around it. The refusal moves from the
// whole package to the CALL.

type counter struct{ n int }

func (c counter) good() int { return c.n + 1 }

func (c counter) rendered() string { return fmt.Sprintf("counter(%d)", c.n) }

func plainGood() int { return 41 }

func quarantineSiblingMethod() int {
	c := counter{n: 4}
	return c.good() + plainGood()
}

func quarantineSiblingPlain() int {
	return plainGood() + 1
}

func quarantineSiblingCall() int {
	c := counter{n: 4}
	return len(c.rendered())
}

func main() {
	println(quarantineSiblingMethod(), quarantineSiblingPlain(), quarantineSiblingCall())
}
