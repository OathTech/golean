package main

// `continue outer` / `break outer` crossing an inner LABELED loop: the
// labeled signals must STRIP the inner loop's label continuation rather
// than matching it (machine arms continueToLabelSkip after
// continueToLoopSkip, and breakToLabelSkip), while `continue inner`
// still matches the inner label. Differential coverage for the labelK
// skip arms (audit-response 2026-08-04, F3 — the arms existed with no
// corpus case exercising them).
func labeledCrossInnerLabeled() int {
	n := 0
outer:
	for i := 0; i < 3; i++ {
	inner:
		for j := 0; j < 4; j++ {
			if j == 0 {
				continue inner
			}
			if i == 2 && j == 2 {
				break outer
			}
			if j == 2 {
				continue outer
			}
			n = n*10 + i + j + 1
		}
	}
	return n
}

func main() {
	labeledCrossInnerLabeled()
}
