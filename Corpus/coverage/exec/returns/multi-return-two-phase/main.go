package main

// Two-phase multi-value return (spec#Return_statements: "return e1,
// .., en" assigns to the result variables LIKE AN ASSIGNMENT — every
// operand evaluates, left to right, BEFORE any result is stored).
// BUG-075 ($GOROOT/test harvest 2026-09-01, fixedbugs/issue43835.go):
// the wire decoder lowered the operands as sequential per-result
// assigns, so operand 1's store landed before operand 2's panic and a
// recover observed the partial store through the results.

// issue43835 g shape: unnamed results. *p panics before `true` may be
// stored; the recovered call must yield the ZERO results.
func retTwoPhaseUnnamed() int {
	bad, _ := retg()
	if bad {
		return 1
	}
	return 0
}

func retg() (bool, int) {
	defer func() { recover() }()
	var p *int
	return true, *p
}

// issue43835 h shape: blank NAMED results (the named-result store path).
func retTwoPhaseBlankNamed() int {
	bad, _ := reth()
	if bad {
		return 1
	}
	return 0
}

func reth() (_ bool, _ int) {
	defer func() { recover() }()
	var p *int
	return true, *p
}

// Control (issue43835 f shape, always-correct assign path): the
// two-phase multi-ASSIGN to named results already held; pinned beside
// the return shapes so the pair moves together.
func retTwoPhaseAssignControl() int {
	if retf() {
		return 1
	}
	return 0
}

func retf() (bad bool) {
	defer func() { recover() }()
	var p *int
	bad, _ = true, *p
	return
}
