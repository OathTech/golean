package main

// F24 frontier enumeration (slice 6; triage row F24): a live channel
// RECEIVE directly in a short-circuit OPERAND. spec#Order_of_evaluation
// orders receive operations and binary logical operations lexically
// left-to-right, and spec#Logical_operators makes the right operand
// CONDITIONAL — so a receive in an RHS operand must run only when the
// left operand does not decide. The E3 conditional normalization
// handles CALLS in that position; receives were scoped out explicitly
// (inventory E3's design note) and refuse at the emit.go hoistChanRecv
// guard: "channel receive in <ctx> (would change evaluation order)".
//
// The and-rhs-skipped row is the load-bearing one: the short circuit
// SKIPS the receive, so the channel keeps its element — an
// unconditional hoist would drain it and change len. Any future lift
// of this refusal must keep that row's 11.
//
// Controls, pinned GREEN: a receive in the LHS operand (unconditional
// position, ordinary hoist) and a receive inside a FUNC LITERAL called
// in the RHS (the E3-normalized call path — the receive is in the
// callee's own body, not the operand).

func trueFn() bool { return true }

func rscAndRhs() int {
	ch := make(chan int, 1)
	ch <- 1
	ok := true
	if ok && <-ch == 1 {
		return 11
	}
	return -1
}

func rscOrRhs() int {
	ch := make(chan int, 1)
	ch <- 2
	done := false
	if done || <-ch == 2 {
		return 21
	}
	return -1
}

func rscAndRhsSkipped() int {
	ch := make(chan int, 1)
	ch <- 3
	ok := false
	if ok && <-ch == 3 {
		return -1
	}
	return len(ch)*10 + 1 // 11: the receive must NOT have happened
}

func rscAndLhs() int {
	ch := make(chan int, 1)
	ch <- 4
	if <-ch == 4 && trueFn() {
		return 41
	}
	return -1
}

func rscFuncLitRhs() int {
	ch := make(chan int, 1)
	ch <- 5
	recv := func() int { return <-ch }
	ok := true
	if ok && recv() == 5 {
		return 51
	}
	return -1
}

func main() {
	rscAndRhs()
	rscOrRhs()
	rscAndRhsSkipped()
	rscAndLhs()
	rscFuncLitRhs()
}
