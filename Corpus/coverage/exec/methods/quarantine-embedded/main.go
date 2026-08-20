package main

import "fmt"

// H-3 edge: the quarantined method is PROMOTED through embedding. The
// promotion wrapper the frontend synthesizes for `wrapper.render` forwards
// to `base.render` — which is the quarantined stub — so `wrapper` keeps a
// complete method set (it still satisfies `describer`, as in Go) and the
// call through the promoted name refuses instead of disappearing.
//
// WHY `fmt.Sprint` AND NOT `fmt.Sprintf` (JC-17, raft W4.1 item 2): the
// unlowerable construct is load-bearing — it is what makes `base.render`
// quarantined at all. The fixture used `fmt.Sprintf` until the W4.1 fmt
// desugar modeled Sprintf/Errorf/Fprintf, at which point this row would
// have flipped green and silently stopped witnessing the quarantine
// shape (the F3 lost-witness class). `fmt.Sprint` is outside the modeled
// three. Any future widening that models it must retarget this fixture
// again, not let the row go green.

type base struct{ n int }

func (b base) plain() int { return b.n + 5 }

func (b base) render() string { return fmt.Sprint(b.n) }

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
