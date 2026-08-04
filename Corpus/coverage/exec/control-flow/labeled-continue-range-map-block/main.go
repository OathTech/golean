package main

// `continue outer` from inside an UNLABELED range-over-map: the
// unwinding meets a mapIterK whose head continuation is the enclosing
// block, NOT the target label, and must strip it (machine arm
// continueToMapIterSkip) before reaching the labeled for loop. The
// observable — how many outer iterations ran — is independent of the
// nondeterministic map iteration order (each outer iteration consumes
// exactly one ranged element, whichever it is). Differential coverage
// for the mapIterK skip arm (audit-response 2026-08-04, F3).
func labeledContinueRangeMapBlock() int {
	m := map[int]int{1: 10, 2: 20, 3: 30}
	n := 0
outer:
	for i := 0; i < 3; i++ {
		for k := range m {
			_ = k
			n++
			continue outer
		}
	}
	return n
}

func main() {
	labeledContinueRangeMapBlock()
}
