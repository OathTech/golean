package main

// spec#Method_declarations block Method_declarations-3-9efcc696: a generic
// type's method receiver re-declares the type parameters — Swap's receiver
// declares A, B and returns Pair[B, A]; First's receiver may rename (First)
// and BLANK a type parameter (Pair[First, _]). Elided bodies realized per
// the obvious semantics.

type Pair[A, B any] struct {
	a A
	b B
}

func (p Pair[A, B]) Swap() Pair[B, A] { return Pair[B, A]{a: p.b, b: p.a} } // receiver declares A, B

func (p Pair[First, _]) First() First { return p.a } // receiver declares First, corresponds to A in Pair

func genericPairSwap() string {
	p := Pair[int, string]{a: 1, b: "x"}
	q := p.Swap()                                                                // Pair[string, int]
	return q.a + "/" + string(rune('0'+q.b)) + "/" + string(rune('0'+p.First())) // "x/1/1"
}
