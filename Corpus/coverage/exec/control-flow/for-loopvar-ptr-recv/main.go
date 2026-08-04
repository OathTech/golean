package main

// Go >= 1.22 per-iteration loop variables, escaping via the IMPLICIT
// ADDRESS a pointer-receiver method takes of its receiver (s.self() is
// (&s).self()): each iteration's cell is distinct, so the saved
// receiver pointers observe 0,1,2. The per-iteration trigger detected
// only func-literal captures, so this escape took the shared-cell
// lowering — silent wrong answer, Lean 333 vs Go 12 (delta-review
// round 2, 2026-08-04).

type lvCounter struct{ n int }

func (p *lvCounter) self() *lvCounter { return p }

func forLoopvarPtrRecv() int {
	var ps []*lvCounter
	for s := (lvCounter{}); s.n < 3; s.n++ {
		ps = append(ps, s.self())
	}
	return ps[0].n*100 + ps[1].n*10 + ps[2].n
}

func main() {
	forLoopvarPtrRecv()
}
