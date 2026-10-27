package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13 — BUG-300, born red:
// a GROUPED var declaration whose later spec reads an earlier spec's NEW
// name. spec#Declarations_and_scope: a variable's scope begins at the end
// of its own VarSpec, so in `var ( x = 1; y = x + 1 )` the second spec's x
// is the NEW x (y = 2) even under an outer x. emitDeclStmt collects the
// group's names into one set and pre-binds ANY initializer that mentions one
// of them to a hoisted temp placed before the whole `var` node — where the
// name still resolves to the outer declaration (or to none). The decoder's
// B6 c4 lexical check catches the disagreement and refuses the WHOLE wire by
// name (status error) on a legal program. Expected = gc go1.26.5.

// F9
func groupedVarReadsNewName() int {
	x := 10
	r := 0
	{
		var (
			x = 1
			y = x + 1 // the NEW x: 2
		)
		r = x*10 + y // 12
	}
	return r*100 + x // 1210
}

// A4
func groupedVarReadsNewNameResult() (x int) {
	x = 10
	{
		var (
			x = 1
			y = x + 1
		)
		if x*10+y != 12 {
			return -1
		}
	}
	return // 10
}

// F9b
func groupedVarNoOuter() int {
	var (
		x = 1
		y = x + 1
	)
	return x*10 + y // 12
}

// F9c
func groupedVarZeroThenRead() int {
	x := 5
	r := 0
	{
		var (
			x int
			y = x + 7
		)
		r = x*10 + y // 7
	}
	return r*100 + x // 705
}

func main() {
	println(groupedVarReadsNewName(), groupedVarReadsNewNameResult(), groupedVarNoOuter(), groupedVarZeroThenRead())
}
