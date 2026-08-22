package main

import "reflect"

// The fail-closed invariant of H-3: a quarantined method is NEVER dropped
// from its type's method set. Dropping it would change INTERFACE
// SATISFACTION — `item` would stop satisfying `stringer`, which it does
// satisfy in Go — and a comma-ok assert would then answer a silently wrong
// `false`. The stub carries the real signature, so satisfaction answers
// what gc answers and only the dispatched CALL refuses.
//
// WHY `reflect.TypeOf` (JC-17, THIRD pick — audit R4-M-1): the
// unlowerable construct here is load-bearing — it is what makes
// `render` quarantined at all. `fmt.Sprintf` lowered when the W4.1
// desugar landed; `fmt.Sprint` lowered when audit R4-M-1 modeled the
// fixed-arity form. The old text here justified REFUSING fmt.Sprint
// by this fixture's needs — a corpus-scoped refusal inversion (common
// Go kept refused to keep a witness stable); the lesson is to pick
// the cause by structural distance from the modeled envelope, not by
// "currently unmodeled". WHY REFLECTION IS FAR: the frontend lowers a
// CLOSED WORLD of statically instantiated types, and reflect.TypeOf
// asks about a value's DYNAMIC type — a question the wire's static
// type channel does not carry. That is a scope statement about this
// frontend, not a claim that reflection is unmodelable in principle.
// No eternal refusal exists: if reflect ever lowers, this row flips
// LOUDLY in the baseline and must be retargeted again, never let go
// green.

type stringer interface {
	tag() int
	render() string
}

type item struct{ n int }

func (i item) tag() int { return i.n * 2 }

func (i item) render() string { return reflect.TypeOf(i.n).String() }

func quarantineIfaceSatisfies() int {
	var x any = item{n: 3}
	if _, ok := x.(stringer); ok {
		return 1
	}
	return 0
}

func quarantineIfaceDispatchGood() int {
	var s stringer = item{n: 3}
	return s.tag()
}

func quarantineIfaceDispatchBad() int {
	var s stringer = item{n: 3}
	return len(s.render())
}

func main() {
	println(quarantineIfaceSatisfies(), quarantineIfaceDispatchGood(), quarantineIfaceDispatchBad())
}
