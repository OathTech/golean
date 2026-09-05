// BUG-097 / BUG-059 panic-text pins (lane fr19-bug097, 2026-09-05; design
// note docs/2026-09-05_fr19-bug097-design.md §1/§2.3/§3): two source
// packages named `inner` at DISTINCT paths (`red/inner`, `blue/inner`).
// Identity is path-keyed (`interface{Get() red/inner.T}` vs
// `interface{Get() blue/inner.T}`), display is gc's name-qualified,
// deliberately ambiguous `interface { Get() inner.T }`. Texts from the
// go1.26.5 probes P2 in docs/evidence/2026-09-05_fr19-bug097/gc-probes.txt.
// The UNEXPORTED-method shape is multipkg/unexported-method-scope (BUG-098).
package main

import (
	bi "blue/inner"
	ri "red/inner"
)

// A red value does not satisfy blue's `interface{ Get() T }` (the result
// type is blue's T): reported as MISSING at runtime.
// gc: interface conversion: inner.T is not interface { Get() inner.T }: missing method Get
func crossAnonMissing() int {
	bi.Assert(ri.Make(1))
	return 0
}

// The operand's STATIC anonymous interface type renders in the
// concrete-target form.
// gc: interface conversion: interface { Get() inner.T } is inner.T, not inner.W
func anonSourceCross() int {
	s := ri.Src()
	return int(s.(ri.W))
}

func main() {
	for _, f := range []func() int{crossAnonMissing, anonSourceCross} {
		func() {
			defer func() { println(recover().(error).Error()) }()
			f()
		}()
	}
}
