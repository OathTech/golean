package main

// Lane frontend/fix-paren-forms-1105 (2026-11-05), the fix of BUG-390: the
// emitter's fallthrough placement check now reads the clause's last
// NON-EMPTY statement, as go/types does (stmt.go stmtList trims trailing
// empty statements first). The shapes around the Cases rows: two trailing
// empty statements after the fallthrough, empty statements BEFORE it (the
// last statement is the branch itself — lowered before the fix too), and
// a clause that is only an empty statement. Expected = gc go1.26.5.

func twoEmpties(x int) int {
	r := 0
	switch x {
	case 1:
		r = 1
		fallthrough
		;
		;
	case 2:
		r += 10
	}
	return r
}

func emptiesBefore(x int) int {
	r := 0
	switch x {
	case 1:
		;
		r = 1
		;
		fallthrough
	case 2:
		r += 10
	default:
		r += 100
	}
	return r
}

func emptyOnlyClause(x int) int {
	r := 0
	switch x {
	case 1:
		;
	case 2:
		r = 2
	}
	return r
}

func main() {
	println(twoEmpties(1), twoEmpties(2), emptiesBefore(1), emptiesBefore(2), emptiesBefore(3), emptyOnlyClause(1), emptyOnlyClause(2))
}
