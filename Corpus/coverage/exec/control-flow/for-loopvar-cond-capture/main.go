package main

// Go >= 1.22 per-iteration loop variables, captured from the for
// clause's CONDITION: the condition of each iteration runs on that
// iteration's own cell, so closures appended by the condition observe
// 0,1,2,3 — not four views of the shared final value. The trigger for
// the per-iteration desugar previously scanned only the BODY for a
// capturing func literal, so a condition capture took the shared-cell
// lowering — silent wrong answer (audit-response 2026-08-04, F2).
func forLoopvarCondCapture() int {
	var fs []func() int
	for i := 0; func() bool {
		fs = append(fs, func() int { return i })
		return i < 3
	}(); i++ {
	}
	total := 0
	for _, f := range fs {
		total = total*10 + f()
	}
	return total
}

func main() {
	forLoopvarCondCapture()
}
