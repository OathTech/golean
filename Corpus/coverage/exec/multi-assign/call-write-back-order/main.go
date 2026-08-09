package main

// Call write-back TARGET-OPERAND TIMING (S1 audit major, 2026-08-09;
// the genre the sibling case target-eval-before-call is structurally
// blind to — its callee never mutates a target operand). For
// `lhs..., x = f(...)` the spec leaves the order of the call against
// the evaluation and indexing of the left-hand operands UNSPECIFIED
// (§Order of evaluation: "the order of those events compared to the
// evaluation and indexing of x and the evaluation of y ... is not
// specified"), but gc deterministically realizes CALL-FIRST: the
// target operands (index operands, the pointer of a deref target, the
// slice-header base) are read AFTER the call returns. The machine
// consumes no Choices here, so per the deterministic-latitude
// precedent (panic identity, hidden-dep init order) it must pin gc's
// realized point. Every subject encodes its observation as one int;
// panics are recovered and encoded.

var xg [2]int
var jg int
var gi int
var a1, b1 int
var pg *int
var sg []int
var first2 []int

// setOob moves the index the pending target x[jg] will use OUT of
// range. gc: index read post-call -> panic (recovered). Operand-first:
// x[0]=42, jg=3, no panic.
func setOob() (int, int) {
	jg = 5
	return 42, 3
}

func indexMissedPanic() int {
	xg = [2]int{0, 0}
	jg = 0
	rec := 0
	func() {
		defer func() {
			if recover() != nil {
				rec = 1
			}
		}()
		xg[jg], jg = setOob()
	}()
	return xg[0]*10000 + xg[1]*1000 + jg*10 + rec
}

// resetIdx moves an initially OUT-OF-RANGE index back in range. gc:
// no panic (index read post-call, =0). Operand-first: spurious panic.
func resetIdx() (int, int) {
	jg = 0
	return 42, 3
}

func indexSpuriousPanic() int {
	xg = [2]int{0, 0}
	jg = 5
	rec := 0
	func() {
		defer func() {
			if recover() != nil {
				rec = 1
			}
		}()
		xg[jg], jg = resetIdx()
	}()
	return xg[0]*10000 + xg[1]*1000 + jg*10 + rec
}

// bumpAndTwo bumps the global index the pending target uses. gc:
// x[2]=42 (post-call read). Operand-first: x[0]=42.
func bumpAndTwo() (int, int) {
	gi = 2
	return 42, 7
}

var x3 [3]int

func globalIndex() int {
	x3 = [3]int{0, 0, 0}
	gi = 0
	x3[gi], gi = bumpAndTwo()
	return x3[0]*10000 + x3[1]*1000 + x3[2]*100 + gi
}

// swapPtr redirects the global pointer the deref target goes through.
// gc: the write lands through the NEW pointer (b1=42). Operand-first:
// through the OLD (a1=42).
func swapPtr() (int, int) {
	pg = &b1
	return 42, 7
}

func derefTarget() int {
	a1, b1 = 0, 0
	pg = &a1
	z := 0
	*pg, z = swapPtr()
	return a1*1000 + b1*100 + z
}

// replace swaps the global slice HEADER the index target's base uses.
// gc: the write lands in the NEW backing. Operand-first: the OLD.
func replaceHeader() (int, int) {
	sg = []int{0, 0}
	return 42, 3
}

func sliceHeaderBase() int {
	first2 = []int{7, 7}
	sg = first2
	z := 0
	sg[1], z = replaceHeader()
	return first2[0]*100000 + first2[1]*10000 + sg[0]*1000 + sg[1]*100 + z
}

// The HOISTED-CALL CONTROL: the same source shape with a single-value
// call is hoisted by the frontend ahead of the statement, so the
// operands are read post-call on BOTH paths — green under either
// order, pinning the internal consistency the write-back path must
// share.
func setIdx() int {
	gi = 2
	return 42
}

func hoistedControl() int {
	x3 = [3]int{0, 0, 0}
	gi = 0
	x3[gi], gi = setIdx(), 3
	return x3[0]*10000 + x3[1]*1000 + x3[2]*100 + gi
}
