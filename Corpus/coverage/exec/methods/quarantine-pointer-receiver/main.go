package main

import "reflect"

// H-3 edge: pointer vs value receiver. The quarantined method is declared
// on `*ptrOnly`, so Go's method-set asymmetry says a VALUE `ptrOnly` does
// not satisfy `ptrIface` while `*ptrOnly` does. The stub must carry the
// pointer receiver type verbatim — a stub recorded with the wrong receiver
// would flip one of these two answers silently.
//
// WHY `reflect.TypeOf` (JC-17, THIRD pick — audit R4-M-1): the
// unlowerable construct here is load-bearing — it is what makes
// `render` quarantined at all. `fmt.Sprintf` lowered when the W4.1
// desugar landed; `fmt.Sprint` lowered when audit R4-M-1 modeled the
// fixed-arity form. The old text here justified REFUSING fmt.Sprint
// by this fixture's needs — a corpus-scoped refusal inversion (common
// Go kept refused to keep a witness stable); the lesson is to pick
// the cause by structural distance from the modeled envelope, not by
// "currently unmodeled". Reflection is the deep-latitude surface the
// closed-world frontend does not model by doctrine. No eternal
// refusal exists: if reflect ever lowers, this row flips LOUDLY in
// the baseline and must be retargeted again, never let go green.

type ptrOnly struct{ n int }

func (p *ptrOnly) bump() int { p.n++; return p.n }

func (p *ptrOnly) render() string { return reflect.TypeOf(p.n).String() }

type ptrIface interface {
	bump() int
	render() string
}

func quarantinePtrValueNotSatisfies() int {
	var x any = ptrOnly{n: 1}
	if _, ok := x.(ptrIface); ok {
		return 1
	}
	return 0
}

func quarantinePtrSatisfies() int {
	var x any = &ptrOnly{n: 1}
	if _, ok := x.(ptrIface); ok {
		return 1
	}
	return 0
}

func quarantinePtrCall() int {
	p := &ptrOnly{n: 1}
	return len(p.render())
}

func main() {
	println(quarantinePtrValueNotSatisfies(), quarantinePtrSatisfies(), quarantinePtrCall())
}
