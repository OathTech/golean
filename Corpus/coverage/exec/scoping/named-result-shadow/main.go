package main

// Named-result SHADOWING pins (W4.3 wave 6, BUG-068 —
// docs/raft-w43-log.md; found by the trace differential's rendered
// tier on confchange_v2_add_double_{auto,implicit}, minimized in
// artifacts/w43/probe-autoleave). The wire carries variable NAMES and
// the machine writes/reads named results by name at the return/exit
// seam, so a local shadowing a named result ALIASED the slot: the
// EnterJoint shape returned false where gc returns true — a silent
// wrong answer at a forced point. The fix renames shadowing locals at
// emit time (object-keyed, resultshadow.go); constructs outside the
// rename set REFUSE (the range-clause boundary row pins that).

// The upstream ConfChangeV2.EnterJoint shape VERBATIM (modulo types).
func enterJointShape() int {
	al, ok := func() (autoLeave bool, ok bool) {
		if true {
			var autoLeave bool
			switch 0 {
			case 0:
				autoLeave = true
			}
			return autoLeave, true
		}
		return false, false
	}()
	out := 0
	if al {
		out += 10
	}
	if ok {
		out += 1
	}
	return out
}

// The outer result survives inner-shadow writes; the bare return reads
// the RESULT slot, not the dead shadow.
func shadowThenBareReturn() (n int, s string) {
	n = 5
	s = "outer"
	{
		n := 99
		s := "inner"
		_ = n
		_ = s
	}
	return
}

func shadowShortDecl() (v int) {
	v = 3
	if true {
		v := 40
		return v + 1 // the INNER v: 41
	}
	return
}

// A deferred write to the REAL named result coexisting with a shadow.
func shadowWithDeferredWrite() (r int) {
	defer func() { r += 100 }()
	{
		var r int
		r = 7
		_ = r
	}
	r = 5
	return r // 5, then the deferred +100 -> 105
}

// ---- fail-closed boundary row (red BY DESIGN): a shadow arising in a
// construct outside the rename set refuses rather than aliasing. ----
func shadowInRangeClause() (i int) {
	i = -1
	for i := range []int{10, 20} {
		_ = i
	}
	return i
}

// ---- R1-C1 (W4.3 audit fix round): the CAPTURE SEAM must follow the
// rename. A closure capturing a renamed shadow receives the SHADOW
// cell's address; before the fix the capture ref was emitted under the
// source name and grabbed the RESULT slot instead — a silent wrong
// answer through the closure (probe .tmp/audit-r1/p9b, p9c). ----

// The closure WRITES the shadow: x(result)=1 survives, +100 -> 101.
func shadowCapturedWrite() (x int) {
	x = 1
	{
		x := 10
		g := func() { x += 5 }
		g()
		_ = x
	}
	return x + 100
}

// The closure READS the shadow: r=10 (the shadow's value, not the
// result slot's 3), so 10*100 + 3 -> 1003.
func shadowCapturedRead() (x int) {
	x = 3
	r := 0
	{
		x := 10
		g := func() int { return x }
		r = g()
	}
	return r*100 + x
}

// ---- R1-C2 (W4.3 audit fix round): the PER-ITERATION CELL machinery
// (emitForPerIteration — a for-init variable captured by a closure gets
// a fresh cell per iteration, Go 1.22 semantics) must follow the rename
// too: its seed ref and cell declarations used the source name, so a
// renamed shadow's cells aliased the result slot and the per-iteration
// freshness was lost (probe .tmp/audit-r1/p4). Go: cells 0,1,2 -> sum
// 3, +1000 -> 1003. ----
func shadowLoopVarCaptured() (x int) {
	var fs []func() int
	for x := 0; x < 3; x++ {
		fs = append(fs, func() int { return x })
	}
	for _, g := range fs {
		x += g()
	}
	return x + 1000
}

func main() {
	n, s := shadowThenBareReturn()
	println(enterJointShape(), n, s, shadowShortDecl(),
		shadowWithDeferredWrite(), shadowInRangeClause(),
		shadowCapturedWrite(), shadowCapturedRead(),
		shadowLoopVarCaptured())
}
