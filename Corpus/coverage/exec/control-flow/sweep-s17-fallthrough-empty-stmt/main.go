package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-172's line, cell A13.2): a `fallthrough` followed by an EXPLICIT
// empty statement is the clause's final non-empty statement
// (spec#Fallthrough_statements; go/types `trimTrailingEmptyStmts` makes
// trailing empty statements invisible to the placement check), so gc runs
// the program; the emitter's placement check reads the clause's LAST
// statement only, so the fallthrough is not recognized and the declaration
// is quarantined with a cause naming fallthrough itself as unsupported
// (BUG-390, found by this sweep). The explicit-semicolon spelling on the
// same line has no empty statement and lowers. Expected = gc go1.26.5.

func fallthroughThenEmptyStmt(x int) int {
	r := 0
	switch x {
	case 1:
		r = 1
		fallthrough
		;
	case 2:
		r += 10
	}
	return r
}

func fallthroughExplicitSemicolon(x int) int {
	r := 0
	switch x {
	case 1:
		r = 1
		fallthrough;
	case 2:
		r += 10
	}
	return r
}

func main() {
	println(fallthroughThenEmptyStmt(1), fallthroughThenEmptyStmt(2), fallthroughExplicitSemicolon(1),
		fallthroughExplicitSemicolon(2))
}
