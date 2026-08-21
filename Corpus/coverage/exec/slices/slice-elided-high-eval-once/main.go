package main

// BUG-066 guardrails: a slice expression with an ELIDED high bound must
// evaluate its base exactly once. The frontend's default-high lowering
// (`len(base)`) re-emitted the base, so a call-valued base ran TWICE —
// gc 1 call, machine 2, status ok (census 2026-08-21 §10 H-a).

func callBase() int {
	calls := 0
	expensive := func() []int {
		calls++
		return []int{10, 20, 30}
	}
	s := expensive()[:]
	return calls*100 + len(s)*10 + s[2]%10
}

func callBaseLowOnly() int {
	calls := 0
	expensive := func() []int {
		calls++
		return []int{10, 20, 30}
	}
	s := expensive()[1:]
	return calls*100 + len(s)*10 + s[0]%10
}

func explicitHighControl() int {
	calls := 0
	expensive := func() []int {
		calls++
		return []int{10, 20, 30}
	}
	s := expensive()[0:3]
	return calls*100 + len(s)*10 + s[2]%10
}
