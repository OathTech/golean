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

func main() {
	n, s := shadowThenBareReturn()
	println(enterJointShape(), n, s, shadowShortDecl(),
		shadowWithDeferredWrite(), shadowInRangeClause())
}
