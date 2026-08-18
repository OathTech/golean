package main

// spec#If_statements + spec#Order_of_evaluation: the if statement's init
// "executes before the expression is evaluated", and within the condition
// the usual operand order applies. These are the BUG-058 wrong-answer
// guardrails (P3 audit B1): the frontend's short-circuit hoisting emits
// the condition's desugar block BEFORE the if, outside the init's scope,
// so a call in the condition's right operand runs before the init.

// condCallAfterInit: go runs a (init) then b (condition) -> order 12.
// The defective lowering runs b first -> 21.
func condCallAfterInit() int {
	order := 0
	a := func() int { order = order*10 + 1; return 1 }
	b := func() int { order = order*10 + 2; return 1 }
	if x := a(); b() == x {
		order = order * 1
	}
	return order
}

// initPanicFirst: the init's s[0] panics before b can run; go never runs
// b (returns 1); the defective lowering runs b first (returns 21).
func initPanicFirst() (out int) {
	ran := 0
	defer func() {
		if recover() != nil {
			out = ran*10 + 1
		}
	}()
	var s []int
	b := func() int { ran = 2; return 0 }
	if x := s[0]; b() == x {
		ran = ran * 1
	}
	return ran
}
