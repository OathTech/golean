// BUG-098 / FR-31 pins (lane fr19-bug097, 2026-09-05; design note
// docs/2026-09-05_fr19-bug097-design.md §2.5): two source packages named
// `inner` at DISTINCT paths, each with an unexported method `get` and its
// own `interface{ get() int }`. spec#Type_identity: unexported method
// names are package-scoped, so red's T does NOT implement blue's
// interface (gc probe P5: `true false`; the failed assert says
// `interface conversion: inner.T is not interface { inner.get() int }:
// missing method get`). The wire's method tables carry BARE names, so the
// machine could answer `true true`: the frontend REFUSES the export by
// name (`unexported interface method name(s) shared across packages: get
// (required by blue/inner, implemented in red/inner); …`). RED BY DESIGN
// at frontend-export until FR-31 qualifies the names.
package main

import (
	bi "blue/inner"
	ri "red/inner"
)

// gc: interface conversion: inner.T is not interface { inner.get() int }: missing method get
func unexportedCrossAssert() int {
	bi.AssertGet(ri.Make(1))
	return 0
}

// gc: true false
func unexportedDistinct() (bool, bool) {
	x := ri.Make(1)
	return ri.IsGet(x), bi.IsGet(x)
}

func main() {
	println(unexportedDistinct())
	func() {
		defer func() { println(recover().(error).Error()) }()
		unexportedCrossAssert()
	}()
}
