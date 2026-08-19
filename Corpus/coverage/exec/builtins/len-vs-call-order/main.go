package main

// The len-vs-CALL forced-point divergence (bug-fix arc triage §3.4;
// slice 6 lands the owed guardrail). spec#Order_of_evaluation orders
// "all function calls, method calls, receive operations, and binary
// logical operations" left-to-right when evaluating an expression's
// operands, and spec#Built-in_functions says built-ins "are called
// like any other function" — so in len(ch) + fill(ch) the len operand
// is read BEFORE the call runs. gc agrees (go1.26.5 probe,
// artifacts/probe/slice6a + the slice-5 triage probe): go run → 1.
//
// The frontend hoists CALLS out of expressions (ANF) but leaves len
// inline in a receive-free function (the fnHasRecv hoist is the only
// thing that ever hoists len), so the machine evaluates fill first and
// reads the post-call len — BUG-023's exact class on the len-vs-CALL
// axis. The two bare rows are pinned RED (differential) until the A6
// mini-slice lands with the corrected predicate ("the statement's
// sweep contains an ORDERED EVENT — receive OR call", triage §3.4).
//
// The recv-bearing row is the ACCIDENT-GREEN control: a function
// containing a live receive hoists len ahead of the call hoist today,
// so it gets len-vs-call RIGHT by accident. Pinning it green means A6
// cannot silently extend the divergence to receive-bearing functions.

func fill(ch chan int) int {
	ch <- 2
	ch <- 3
	return 0
}

func lenVsCallChan() int {
	ch := make(chan int, 4)
	ch <- 1
	return len(ch) + fill(ch) // spec: len first -> 1; wrong order reads 3
}

func growSlice(s *[]int) int {
	*s = append(*s, 9, 9)
	return 0
}

func lenVsCallSlice() int {
	s := []int{1}
	return len(s) + growSlice(&s)*10 // spec: len first -> 1; wrong order reads 3
}

func lenVsCallRecvBearing() int {
	ch := make(chan int, 4)
	ch <- 1
	sink := make(chan int, 1)
	sink <- 5
	v := len(ch) + fill(ch) // fnHasRecv hoists len here: correct by accident
	return v*10 + <-sink    // 1*10 + 5
}

func main() {
	lenVsCallChan()
	lenVsCallSlice()
	lenVsCallRecvBearing()
}
