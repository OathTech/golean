package main

// The ANONYMOUS empty-struct literal on the LEFT of a comparison, so the
// frontend's operandType is the UNNAMED struct{} side and the defined-type
// operand is the one mismatching the context — the reverse operand orders
// of empty-struct-literal-at-named-type/compare, plus an expression-switch
// tag (its case test compares at the anonymous tag's type). Delta-review
// R1, 2026-08-05: the F4 equality-site tightening required the mismatching
// operand's OWN tag to be canonical and stuck these legal comparisons; the
// guard is pair-level (either operand canonical, or equal tags at a
// canonical context) — two DIFFERENT defined empty types still stick.

type leftMarker struct{}

func emptyStructLeftEq() int {
	m := leftMarker{}
	if struct{}{} == m {
		return 1
	}
	return 0
}

func emptyStructLeftNeq() int {
	m := leftMarker{}
	if struct{}{} != m {
		return 0
	}
	return 2
}

func emptyStructLeftSwitch() int {
	m := leftMarker{}
	switch struct{}{} {
	case m:
		return 3
	default:
		return 0
	}
}
