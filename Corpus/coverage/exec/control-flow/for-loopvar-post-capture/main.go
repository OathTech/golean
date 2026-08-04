package main

// Go >= 1.22 per-iteration loop variables, captured from the for
// clause's POST statement: the post statement of iteration k runs on
// the FRESHLY declared variable of iteration k+1 ("declared before
// executing the post statement and initialized to the value of the
// previous iteration's variable"), so closures created by the post
// observe 1,2,3 — distinct cells, not one shared cell. The trigger for
// the per-iteration desugar previously scanned only the BODY for a
// capturing func literal; this hole PRE-DATES the control-flow slice
// (the plain path accepted post statements with calls before it), same
// mechanism as the condition hole (audit-response 2026-08-04, F2).
func forLoopvarPostCapture() int {
	var fs []func() int
	grab := func(f func() int) int {
		fs = append(fs, f)
		return 1
	}
	for i := 0; i < 3; i = i + grab(func() int { return i }) {
	}
	total := 0
	for _, f := range fs {
		total = total*10 + f()
	}
	return total
}

func main() {
	forLoopvarPostCapture()
}
