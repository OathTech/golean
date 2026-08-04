package main

// A backward goto re-executing `var b nestedRecvBox`, where a
// pointer-receiver method is called on a FIELD of b (b.in.self() takes
// &b.in implicitly): Go's fresh struct per execution means the two
// captured receiver pointers refer to different cells; the hoisted
// lowering would alias one cell — silent wrong answer. The frontend
// must refuse (fidelity envelope; audit-response 2026-08-04: the
// original receiver check only caught x.M() on a bare identifier, not
// nested selections). Pins the frontend-export refusal.

type nestedRecvInner struct{ n int }

func (p *nestedRecvInner) self() *nestedRecvInner { return p }

type nestedRecvBox struct{ in nestedRecvInner }

func gotoBackwardNestedRecv() int {
	var first, second *nestedRecvInner
	i := 0
loop:
	var b nestedRecvBox
	b.in.n = i + 1
	if i == 0 {
		first = b.in.self()
	} else {
		second = b.in.self()
	}
	i++
	if i < 2 {
		goto loop
	}
	return first.n*10 + second.n
}

func main() {
	gotoBackwardNestedRecv()
}
