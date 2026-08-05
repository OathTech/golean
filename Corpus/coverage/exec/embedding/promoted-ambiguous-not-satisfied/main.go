package main

// Promotion NEGATIVE polarity (BUG-007 fix guardrail): two embedded fields
// at the SAME depth both declare m, so m is not in the outer method set at
// all (Go's ambiguity exclusion) — the interface is NOT satisfied and the
// comma-ok assert answers false. Pins that removing the BUG-007
// fail-closure gives the definite-false answer only where Go does.

type ambigIface interface {
	m() int
}

type ambigA struct {
	n int
}

func (a ambigA) m() int {
	return a.n
}

type ambigB struct {
	k int
}

func (b ambigB) m() int {
	return b.k
}

type ambigOuter struct {
	ambigA
	ambigB
}

func promotedAmbiguousNotSatisfied() int {
	var x any = ambigOuter{}
	_, ok := x.(ambigIface)
	if ok {
		return 1
	}
	return 0
}
