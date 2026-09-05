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
	"emb"
	ri "red/inner"
)

// DISTINCT-NAME shape (audit fix round R4, 2026-09-05): S promotes emb's
// unexported `get` — that is `emb.get`, not `main.get` — so S does NOT
// implement main's `interface{ get() int }`. gc: false. On main before this
// lane the bare-name tables matched and the machine answered TRUE (a
// silent wrong answer — the same-name shape above was refused by accident,
// this one was not); the guard now refuses the export by name.
type S struct{ emb.E }

type J interface{ get() int }

// gc: false
func unexportedDistinctNames() bool {
	var x any = S{}
	_, ok := x.(J)
	return ok
}

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
	println(unexportedDistinctNames())
	func() {
		defer func() { println(recover().(error).Error()) }()
		unexportedCrossAssert()
	}()
}
