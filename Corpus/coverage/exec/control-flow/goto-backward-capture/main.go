package main

// A backward goto re-executing a declaration whose variable is CAPTURED
// by a func literal: Go gives each execution of the declaration a fresh
// cell, so the two closures observe different cells. The dispatch-loop
// restructuring hoists top-level declarations to one shared cell, which
// would be a silent wrong answer here — the frontend REJECTS this shape
// (the design note's envelope, docs/2026-08-04_control-flow-design.md),
// so this case pins the visible frontend-export refusal.
func gotoBackwardCapture() int {
	var fs []func() int
	i := 0
loop:
	x := i * 10
	fs = append(fs, func() int { return x })
	i++
	if i < 2 {
		goto loop
	}
	fs[0]()
	return fs[0]() + fs[1]()
}

func main() {
	gotoBackwardCapture()
}
