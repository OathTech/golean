package main

// Go >= 1.22 per-iteration loop variables, escaping by EXPLICIT ADDRESS
// (&i in the body): each iteration's cell is distinct, so the saved
// pointers observe 0,1,2 — not three views of one shared cell. The
// per-iteration trigger detected only func-literal CAPTURES (a
// predicate predating the control-flow slice), so an address escape
// took the shared-cell lowering — silent wrong answer, Lean 333 vs
// Go 12 (delta-review round 2, 2026-08-04).
func forLoopvarAddrEscape() int {
	var ps []*int
	for i := 0; i < 3; i++ {
		ps = append(ps, &i)
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2]
}

func main() {
	forLoopvarAddrEscape()
}
