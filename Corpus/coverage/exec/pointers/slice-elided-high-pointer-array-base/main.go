package main

// BUG-066 guardrail, array-base form: slicing an array reached through a
// pointer-returning call, with an elided high bound. The array base slices
// through its ADDRESS, and the default-high `len` re-emitted the whole
// operand — so `pf()` ran twice (census 2026-08-21 §10 H-a; the auditor's
// corrected witness — a VALUE-returning call is not addressable, so the
// pointer-returning form is the one that slices legally).

type box struct{ arr [4]int }

func sliceElidedHighPointerArrayBase() int {
	calls := 0
	b := box{arr: [4]int{1, 2, 3, 4}}
	pf := func() *box {
		calls++
		return &b
	}
	s := pf().arr[2:]
	return calls*100 + len(s)*10 + s[0]
}
