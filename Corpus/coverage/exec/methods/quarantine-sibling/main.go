package main

import "fmt"

// Per-declaration quarantine for METHODS (H-3): one method the frontend
// cannot lower (`fmt.Sprint` — outside the W4.1 fmt desugar's modeled
// Sprintf/Errorf/Fprintf set; the fixture moved off `fmt.Sprintf` when
// that desugar landed and these witnesses would have flipped green,
// masking the quarantine shape they pin) must not block the export of
// the methods, functions, and types around it. The refusal moves from the
// whole package to the CALL.

type counter struct{ n int }

func (c counter) good() int { return c.n + 1 }

func (c counter) rendered() string { return fmt.Sprint(c.n) }

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
