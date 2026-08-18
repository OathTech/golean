package main

// spec#Expression_switches block Expression_switches-2-8d84f981: the
// three example switches. (1) cases are matched by VALUE regardless of
// clause order — the default clause runs only when no case matches,
// even though it is written FIRST; multi-value case lists match any
// listed value. (2) "missing switch expression means true", with an
// init statement (switch x := f(); { ... }). (3) case expressions are
// evaluated top-to-bottom, the FIRST match runs (x < y wins over
// x < z when both hold). Adaptation: s1/s2/s3, f1/f2/f3 return arm
// labels instead of printing.
// Expected: tag 0-3 -> 1; tag 4-7 -> 2; other tags -> 3.
// noExpr: f() < 0 -> -f(), else f().
// firstMatch (y=0, z=1): x=-5 -> f1(=1); x=0 -> f2(=2) (0 < 1);
// x=4 -> f3(=3); x=9 -> no case runs -> 0.

func exprSwitchTag(tag int) int {
	s1 := func() int { return 1 }
	s2 := func() int { return 2 }
	s3 := func() int { return 3 }
	r := 0
	switch tag {
	default:
		r = s3()
	case 0, 1, 2, 3:
		r = s1()
	case 4, 5, 6, 7:
		r = s2()
	}
	return r
}

func exprSwitchNoExpr(v int) int {
	f := func() int { return v }
	switch x := f(); { // missing switch expression means "true"
	case x < 0:
		return -x
	default:
		return x
	}
}

func exprSwitchFirstMatch(x int) int {
	y, z := 0, 1
	f1 := func() int { return 1 }
	f2 := func() int { return 2 }
	f3 := func() int { return 3 }
	r := 0
	switch {
	case x < y:
		r = f1()
	case x < z:
		r = f2()
	case x == 4:
		r = f3()
	}
	return r
}

func main() {
	exprSwitchTag(5)
}
