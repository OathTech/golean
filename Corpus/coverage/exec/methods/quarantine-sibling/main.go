package main

import "reflect"

// Per-declaration quarantine for METHODS (H-3): one method the frontend
// cannot lower must not block the export of the methods, functions, and
// types around it. The refusal moves from the whole package to the CALL.
// The unlowerable cause is `reflect.TypeOf` — the THIRD pick (JC-17,
// audit R4-M-1): `fmt.Sprintf` lowered with the W4.1 desugar,
// `fmt.Sprint` lowered when R4-M-1 modeled the fixed-arity form (this
// file was the near-miss the audit round CAUGHT mid-slice: the row had
// already flipped green — the exact lost-witness class this comment
// warns about). WHY REFLECTION IS FAR: the frontend lowers a CLOSED
// WORLD of statically instantiated types, and reflect.TypeOf asks
// about a value's DYNAMIC type — a question the wire's static type
// channel does not carry. That is a scope statement about this
// frontend, not a claim that reflection is unmodelable in principle;
// if it ever lowers, the baseline flags the flip loudly — retarget
// again, never let it go green.

type counter struct{ n int }

func (c counter) good() int { return c.n + 1 }

func (c counter) rendered() string { return reflect.TypeOf(c.n).String() }

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
