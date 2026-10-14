package main

// RED BY DESIGN (BUG-129, [USER] Mike 2026-10-14): at package level gc never
// evaluates a blank field's operand at all, calls included (staticinit.initplan,
// sched.go:545 — no plan entry, no init-time statement); a call there is not
// an admitted operand, so the initializer refuses by name and the export
// with it (FAIL/frontend-export, by-design/blank-field-operand). gc: no bump
// runs — 20.

type blankPkgS struct {
	_ int
	X int
	_ int
}

var blankPkgCnt = 0

func blankPkgBump() int { blankPkgCnt++; return blankPkgCnt * 10 }

var blankPkgW = blankPkgS{blankPkgBump(), 2, blankPkgBump()}

func blankPkgInitCall() int { return blankPkgW.X*10 + blankPkgCnt }
