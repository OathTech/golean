package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: short variable
// REDECLARATION (spec#Short_variable_declarations: `:=` redeclares only
// variables of the SAME block) — in a nested block both names are new, a
// reused name keeps its cell (seen through a closure), a captured variable
// redeclared by mixing stays the one cell, the right-hand side reads the OLD
// value, a blank beside an outer name declares anew. scoping/short-decl-mixing
// holds the same-block form. Expected = gc go1.26.5.

func two() (int, int)   { return 7, 8 }
func three() (int, int) { return 9, 10 }

// E2
func nestedScopeAllNew() int {
	a := 1
	{
		a, b := 2, 3
		_ = a
		_ = b
	}
	return a // 1
}

// E3
func errReusedThroughClosure() int {
	x, e := two()
	f := func() int { return e }
	y, e := three()
	return f()*1000 + x + y + e // 10026
}

// E4
func capturedRedeclared() int {
	x := 1
	f := func() int { return x }
	x, y := 2, 3
	return f()*10 + y // 23
}

// E5
func rhsReadsOld() int {
	a := 5
	a, b := 9, a
	return a*10 + b // 95
}

// E6
func blankAndOuter() int {
	b := 1
	{
		_, b := two()
		if b != 8 {
			return -1
		}
	}
	return b // 1
}

func main() {
	println(nestedScopeAllNew(), errReusedThroughClosure(), capturedRedeclared(), rhsReadsOld(), blankAndOuter())
}
