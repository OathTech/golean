package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// SWITCH CASES and COMPARISON OPERANDS beyond BUG-017's rows: an untyped float
// / rune / nil / multi-value case against an interface tag (the constant takes
// its default type), a constant TAG against an interface case, a defined-type
// tag, the tagless switch and `==` / `!=` with float and rune constants, the
// init form, and the type switch's bound variable re-boxed into `any` from a
// concrete clause.

type tDef int

func mkAny() any { return 1 }

func caseFloat() int {
	var x any = 2.5
	switch x {
	case 2:
		return 2
	case 2.5:
		return 1
	}
	return 0
}

func caseRune() int {
	var x any = 'a'
	switch x {
	case 97:
		return 2
	case 'a':
		return 1
	}
	return 0
}

func caseNil() (int, int) {
	var x any
	var p *tDef
	var y any = p
	a, b := 0, 0
	switch x {
	case nil:
		a = 1
	}
	switch y {
	case nil:
		b = 1
	default:
		b = 2
	}
	return a, b
}

func caseMulti() int {
	var x any = "s"
	switch x {
	case 1, "s":
		return 1
	case 2.5, 'a':
		return 2
	}
	return 0
}

func tagConstCaseAny() (int, int) {
	var x any = 2.5
	var y any = 2
	a, b := 0, 0
	switch 2.5 {
	case x:
		a = 1
	}
	switch 2.0 {
	case y:
		b = 1
	default:
		b = 2
	}
	return a, b
}

func tagDefinedCaseAny() int {
	var x any = tDef(3)
	switch tDef(3) {
	case x:
		return 1
	}
	return 0
}

func noTag() (int, int) {
	var x any = 1.5
	var y any = 'a'
	a, b := 0, 0
	switch {
	case x == 1:
		a = 2
	case x == 1.5:
		a = 1
	}
	switch {
	case y != 'a':
		b = 2
	case y == 'a' && y != 97:
		b = 1
	}
	return a, b
}

func initForm() int {
	switch x := mkAny(); x {
	case 1.0:
		return 2
	case 1:
		return 1
	}
	return 0
}

func bindingReboxed() (any, any) {
	var x any = tDef(3)
	var y any = 4
	var a, b any
	switch v := x.(type) {
	case tDef:
		a = v
	}
	switch v := y.(type) {
	case int:
		b = v
	}
	return a, b
}

func main() {
	caseFloat()
}
