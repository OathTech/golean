package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-172's line): labeled statements at the shapes emitLabeled and the
// decoder's `labeled` arm did not have rows for — a label on a `var`
// declaration and on a bare block reached by goto, one label that is both a
// goto target and a break target, a label on the per-iteration `for`
// desugar (a block whose trailing statement is the loop) used by `continue`
// and by `break`, a label on a `for` with a condition hoist and with a post
// statement, and one label name in two functions. Expected = gc go1.26.5.

func lt(a, b int) bool { return a < b }

// A1.11
func labeledVarDeclGoto() int {
	i := 0
L:
	var x = i + 1
	i = x
	if i < 3 {
		goto L
	}
	return i // 3
}

// A2.5
func labeledBlockGoto() int {
	n := 0
L:
	{
		n++
		if n < 3 {
			goto L
		}
	}
	return n // 3
}

func labeledEmptyBlockForward() int {
	n := 5
	goto L
L:
	{
	}
	return n // 5
}

// A2.8
func gotoAndBreakSameLabel() int {
	n := 0
L:
	for {
		n++
		if n < 5 {
			break L
		}
	}
	if n < 3 {
		goto L
	}
	return n // 3
}

// A2.9
func periterLabeledContinue() int {
	var fs []func() int
L:
	for i := 0; i < 4; i++ {
		if i%2 == 0 {
			continue L
		}
		fs = append(fs, func() int { return i })
	}
	return fs[0]()*10 + fs[1]() // 13
}

func periterLabeledBreak() int {
	var fs []func() int
L:
	for i := 0; i < 4; i++ {
		fs = append(fs, func() int { return i })
		if i == 1 {
			break L
		}
	}
	return fs[0]()*100 + fs[1]()*10 + len(fs) // 12
}

// A2.15
func labeledForCondCallContinue() int {
	n := 0
L:
	for i := 0; lt(i, 5); i++ {
		if i%2 == 1 {
			continue L
		}
		n += i
	}
	return n // 6
}

// A2.16
func labeledForPostContinueFromRange() int {
	n := 0
L:
	for i := 0; i < 3; i++ {
		for _, v := range []int{1, 2} {
			if v == 2 {
				continue L
			}
			n += i*10 + v
		}
	}
	return n // 1 + 11 + 21 = 33
}

// A2.17
func sameLabelA() int {
	n := 0
L:
	for i := 0; i < 10; i++ {
		n += i
		if i == 2 {
			break L
		}
	}
	return n // 3
}

func sameLabelB() int {
	n := 0
L:
	for i := 0; i < 10; i++ {
		if i == 1 {
			continue L
		}
		n += i
		if i == 3 {
			break L
		}
	}
	return n // 0+2+3 = 5
}

func sameLabelTwoFuncs() int {
	return sameLabelA()*10 + sameLabelB() // 35
}

func main() {
	println(labeledVarDeclGoto(), labeledBlockGoto(), labeledEmptyBlockForward(), gotoAndBreakSameLabel(),
		periterLabeledContinue(), periterLabeledBreak(), labeledForCondCallContinue(), labeledForPostContinueFromRange(),
		sameLabelTwoFuncs())
}
