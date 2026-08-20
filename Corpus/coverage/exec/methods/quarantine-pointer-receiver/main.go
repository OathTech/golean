package main

import "fmt"

// H-3 edge: pointer vs value receiver. The quarantined method is declared
// on `*ptrOnly`, so Go's method-set asymmetry says a VALUE `ptrOnly` does
// not satisfy `ptrIface` while `*ptrOnly` does. The stub must carry the
// pointer receiver type verbatim — a stub recorded with the wrong receiver
// would flip one of these two answers silently.
//
// WHY `fmt.Sprint` AND NOT `fmt.Sprintf` (JC-17, raft W4.1 item 2): the
// unlowerable construct is load-bearing — it is what makes `render`
// quarantined at all. The fixture used `fmt.Sprintf` until the W4.1 fmt
// desugar modeled Sprintf/Errorf/Fprintf, at which point this row would
// have flipped green and silently stopped witnessing the quarantine
// shape (the F3 lost-witness class). `fmt.Sprint` is outside the modeled
// three. Any future widening that models it must retarget this fixture
// again, not let the row go green.

type ptrOnly struct{ n int }

func (p *ptrOnly) bump() int { p.n++; return p.n }

func (p *ptrOnly) render() string { return fmt.Sprint(p.n) }

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
