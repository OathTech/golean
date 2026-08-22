package main

import "reflect"

// H-3 edge: the quarantined method is PROMOTED through embedding. The
// promotion wrapper the frontend synthesizes for `wrapper.render` forwards
// to `base.render` — which is the quarantined stub — so `wrapper` keeps a
// complete method set (it still satisfies `describer`, as in Go) and the
// call through the promoted name refuses instead of disappearing.
//
// WHY `reflect.TypeOf` (JC-17, THIRD pick — audit R4-M-1): the
// unlowerable construct here is load-bearing — it is what makes
// `base.render` quarantined at all. `fmt.Sprintf` lowered when the W4.1
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

type base struct{ n int }

func (b base) plain() int { return b.n + 5 }

func (b base) render() string { return reflect.TypeOf(b.n).String() }

type wrapper struct{ base }

type describer interface {
	plain() int
	render() string
}

func quarantinePromotedGood() int {
	w := wrapper{base{n: 2}}
	return w.plain()
}

func quarantinePromotedSatisfies() int {
	var x any = wrapper{base{n: 2}}
	if _, ok := x.(describer); ok {
		return 1
	}
	return 0
}

func quarantinePromotedCall() int {
	w := wrapper{base{n: 2}}
	return len(w.render())
}

func main() {
	println(quarantinePromotedGood(), quarantinePromotedSatisfies(), quarantinePromotedCall())
}
