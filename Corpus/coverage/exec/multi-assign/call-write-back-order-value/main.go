package main

// The .callValue HALF of the BUG-052 order pin (delta-review minor,
// 2026-08-09): the call-first reorder changed BOTH call paths, but the
// sibling family call-write-back-order/* pins only the named-function
// (.call) path — every callee there is a package-level func. These
// subjects call through a function VALUE (a *types.Var callee, which
// tools/nativefrontend emits as "call-value"), with the callee mutating
// a target operand, so they discriminate the .callValue write-back's
// operand timing: call-first (gc's realized point, pinned) reads the
// index/pointer AFTER the call; the retired operand-first order read
// it before. Single-VALUE calls through values are hoisted by the
// frontend (like the sibling family's hoisted-control), so only the
// multi-value forms discriminate.

var pva [3]int
var pvi int
var pa1, pb1 int
var pvp *int

func pvBump() (int, int) {
	pvi = 2
	return 42, 7
}

// gc: pva[2]=42 (index read post-call). Operand-first: pva[0]=42.
func valueCallIndexTarget() int {
	pva = [3]int{0, 0, 0}
	pvi = 0
	fv := pvBump
	pva[pvi], pvi = fv()
	return pva[0]*10000 + pva[1]*1000 + pva[2]*100 + pvi
}

func pvSwap() (int, int) {
	pvp = &pb1
	return 42, 7
}

// gc: the write lands through the NEW pointer (pb1=42).
// Operand-first: through the OLD (pa1=42).
func valueCallDerefTarget() int {
	pa1, pb1 = 0, 0
	pvp = &pa1
	z := 0
	fv := pvSwap
	*pvp, z = fv()
	return pa1*1000 + pb1*100 + z
}
