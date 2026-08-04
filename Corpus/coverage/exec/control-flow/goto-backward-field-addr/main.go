package main

// A backward goto re-executing `var s S`, with the address of a FIELD of
// s escaping (&s.v): Go gives each execution of the declaration a fresh
// struct, so the two saved pointers refer to DIFFERENT cells. The
// dispatch-loop restructuring hoists s to one shared cell, which would
// be a silent wrong answer — the frontend must refuse (fidelity
// envelope, docs/2026-08-04_control-flow-design.md; audit-response
// 2026-08-04: the original check only caught &x on a bare identifier).
// This case pins the visible frontend-export refusal.

type fieldAddrS struct{ v int }

func gotoBackwardFieldAddr() int {
	var ps []*int
	i := 0
loop:
	var s fieldAddrS
	s.v = i
	ps = append(ps, &s.v)
	i++
	if i < 2 {
		goto loop
	}
	return *ps[0]*10 + *ps[1]
}

func main() {
	gotoBackwardFieldAddr()
}
