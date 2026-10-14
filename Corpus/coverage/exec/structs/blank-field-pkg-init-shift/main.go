package main

// RED BY DESIGN (BUG-130, [USER] Mike 2026-10-14): a package-level literal's
// blank operand is never evaluated by gc (staticinit.initplan skips the
// field), so `1 << n` with n = -1 never panics there — gc 2; the shift is not
// an admitted operand, so the initializer refuses by name, and because a
// shift by a non-constant is not H-11 effect-isolated (it can panic) the
// WHOLE export refuses — not a per-declaration poison (that is the
// effect-isolated case, `S{x + 1, 2}`: the reader refuses, an unread var
// runs). FAIL/frontend-export, by-design/blank-field-operand.

type blankPkgShiftS struct {
	_ int
	X int
}

var blankPkgN = -1

var blankPkgSh = blankPkgShiftS{1 << blankPkgN, 2}

func blankPkgInitShift() int { return blankPkgSh.X }
