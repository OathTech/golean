package main

// Sweep S8 (lane sweep/s8-unseq, 2026-10-27): the target side — the S6/S7 lanes' handover
// cells: a later target's operand against an earlier right-hand call that mutates it; two
// panicking target operands beside a multi-value call (inventory E3's shape WITH an event:
// the E5b graph + the E6a trigger envelope it); a target operand's panic against a
// right-hand panic with a call in the statement. All three admitted: membership rows with
// gc's draw inside. The CALL-FREE general forms (E3/E4 with no event) are BUG-312's rows
// (sweep-s8-general-form).

func f6() (int, int) { return 1, 2 }

func laterTargetOperandVsEarlierCall() int {
	x := []int{0, 0}
	y := []int{0, 0}
	j := 0
	f := func() int { j = 1; return 7 }
	g := func() int { return 3 }
	x[0], y[j] = f(), g()
	return x[0]*100 + y[0]*10 + y[1]
}

func twoPanickingTargetsMultiCall() int {
	aa := [][]int{}
	b := []int{1}
	var pn *int
	aa[5][0], b[*pn] = f6()
	return 0
}

func targetPanicVsRhsPanicWithCall() int {
	xs := []int{1}
	ys := []int{1}
	zs := []int{1}
	f := func() int { return 2 }
	var b int
	xs[ys[9]], b = zs[7], f()
	return b
}
