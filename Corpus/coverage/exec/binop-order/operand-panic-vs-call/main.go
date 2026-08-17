package main

// F1 probes (spec-truth P2, CH2O-note finding F1): intra-expression
// non-call operand order for binary operators. The spec orders
// function calls left-to-right (spec#Order_of_evaluation) but leaves
// the other operand events' order unspecified. gc's observed
// realization (go1.26.5, identical under -gcflags=all='-N -l'):
// CALLS evaluate before non-call operand events even when the
// panicking/reading non-call operand sits lexically LEFT of the call;
// among non-call operands, left before right.
//
// The call-order subjects use a pure observable: the call MUTATES the
// state the left operand reads. Call-first => defined value;
// left-operand-first => panic "index out of range [8]". gc: value.

// Both operands' indexes out of range: the panic names the LEFT index.
func binopLeftIndexFirst() int {
	a := []int{1, 2, 3}
	b := []int{4, 5, 6}
	i, j := 8, 9
	return a[i] / b[j]
}

// Call on the right mutates the index the left operand reads.
// gc: 11 (call ran first, i became 0, a[0]+10).
func binopCallBeforeLeftIndex() int {
	a := []int{1, 2, 3}
	i := 8
	f := func() int { i = 0; return 10 }
	return a[i] + f()
}

// Call in the divisor replaces the slice the left operand indexes.
// gc: 7 (call ran first, a[8] valid in the new slice).
func binopCallBeforeLeftDiv() int {
	a := []int{1, 2, 3}
	f := func() int { a = []int{0, 0, 0, 0, 0, 0, 0, 0, 7}; return 1 }
	return a[8] / f()
}
