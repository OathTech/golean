package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: BUG-142's shape — a
// declaration whose initializer mentions the name it declares, so the
// initializer must read the OUTER cell (spec#Declarations_and_scope: the
// scope begins at the END of the ShortVarDecl / VarSpec) — at every define
// path of the emitter beside the two BUG-142 rows hold: the two-name forms whose RHS reads the outer,
// the typed var form, if/for inits, the select case, the one- and two-target
// receives, the comma-ok assertion (the comma-ok MAP read `v, ok := m[v]`
// refuses by name — «multi-value expression hoisted as a single value» — a
// gap, probed in the lane's report), builtin / conversion /
// assertion / field / deref / index right-hand sides, a keyed literal whose
// field keys carry the name, and a func literal that captures the outer cell.
// Sites: emitAssign's define pre-binding (containsVarUse), emitDeclStmt,
// emitChanRecvAssign, the comma-ok type-assert statement, selectRecvClause.
// The grouped VarSpec whose LATER spec reads an EARLIER spec's new name is
// scoping/sweep-s13-grouped-var-spec (BUG-300, born red). Expected = gc.

type pt struct{ x, f int }

// F10
func varTwoNamesRhsOuter() int {
	x := 5
	{
		var x, y = 1, x
		return x*10 + y // 15
	}
}

// F10b
func defineTwoNamesRhsOuter() int {
	x := 5
	{
		x, y := 1, x
		return x*10 + y // 15
	}
}

// F11
func varTypedSelf() int {
	x := 5
	{
		var x int = x + 1
		return x // 6
	}
}

// F14
func ifInitSelf() int {
	x := 5
	if x := x + 1; x > 0 {
		return x // 6
	}
	return -1
}

// F15
func forInitSelf() int {
	x := 5
	sum := 0
	for x := x + 1; x < 9; x++ {
		sum += x
	}
	return sum*10 + x // 215
}

// F16
func selectCaseSelf() int {
	x := make(chan int, 1)
	x <- 3
	select {
	case x := <-x:
		return x * 2 // 6
	}
}

// F17
func recvSelf() int {
	x := make(chan int, 1)
	x <- 4
	{
		x := <-x
		return x * 2 // 8
	}
}

// F18
func recvTwoSelf() int {
	x := make(chan int, 1)
	x <- 5
	{
		x, ok := <-x
		if !ok {
			return -1
		}
		return x * 2 // 10
	}
}

// F19
func assertTwoSelf() int {
	var v any = 6
	{
		v, ok := v.(int)
		if !ok {
			return -1
		}
		return v * 2 // 12
	}
}

// F21b
func builtinSelf() int {
	s := []int{1, 2, 3}
	{
		s := len(s)
		return s * 2 // 6
	}
}

// F21c
func conversionSelf() int64 {
	x := 7
	{
		x := int64(x) * 2
		return x // 14
	}
}

// F21d
func assertOneSelf() int {
	var x any = 8
	{
		x := x.(int) * 2
		return x // 16
	}
}

// F21e
func fieldSelf() int {
	x := pt{x: 3, f: 9}
	{
		x := x.f
		return x // 9
	}
}

// F21f
func derefSelf() int {
	v := 11
	x := &v
	{
		x := *x
		return x // 11
	}
}

// F21g
func indexSelf() int {
	x := []int{1, 12, 3}
	{
		x := x[1]
		return x // 12
	}
}

// F22
func keyedLiteralSelf() int {
	x := 4
	{
		x := pt{x: x, f: 1}
		return x.x*10 + x.f // 41
	}
}

// F23
func litCapturesOuter() int {
	x := 5
	{
		x := func() int { return x + 1 }
		return x() // 6
	}
}

// F24
func varLitCapturesOuter() int {
	x := 5
	{
		var x = func() int { return x + 2 }
		return x() // 7
	}
}

func main() {
	println(varTwoNamesRhsOuter(), defineTwoNamesRhsOuter(), varTypedSelf(), ifInitSelf(), forInitSelf(),
		selectCaseSelf(), recvSelf(), recvTwoSelf(), assertTwoSelf(),
		builtinSelf(), conversionSelf(), assertOneSelf(), fieldSelf(), derefSelf(), indexSelf(), keyedLiteralSelf(),
		litCapturesOuter(), varLitCapturesOuter())
}
