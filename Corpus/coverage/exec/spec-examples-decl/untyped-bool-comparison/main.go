package main

// spec#Comparison_operators block Comparison_operators-2-60d7731d: a
// comparison yields an UNTYPED boolean — the constant c = 3 < 4 is the
// untyped constant true, and x == y (with x, y int zero-valued, hence true)
// initializes b3 as bool, b4 as bool, and b5 as the user-declared MyBool by
// the usual assignment rules. b5's MyBool identity is observed by
// conversion-free assignment to another MyBool.

const c = 3 < 4 // c is the untyped boolean constant true

type MyBool bool

var x, y int

var (
	// The result of a comparison is an untyped boolean.
	// The usual assignment rules apply.
	b3        = x == y // b3 has type bool
	b4 bool   = x == y // b4 has type bool
	b5 MyBool = x == y // b5 has type MyBool
)

func untypedBoolComparison() int {
	n := 0
	if c {
		n++
	}
	var cb bool = c   // untyped constant true adapts to bool
	var cm MyBool = c // ... and to MyBool
	if cb && bool(cm) {
		n++
	}
	if b3 && b4 {
		n++
	}
	var mb MyBool = b5 // b5 already has type MyBool: no conversion
	if mb {
		n++
	}
	return n // 4
}
