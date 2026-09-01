package main

// BUG-079 (audit fix round 2026-09-01, the issue53619 residual of the
// $GOROOT/test harvest): a comma-ok type assertion assigned into
// INTERFACE-typed targets owes an implicit boxing of the asserted
// component (spec#Type_assertions writes `var v, ok interface{} = x.(T)`),
// which the tuple-producing type-assert statement cannot express. The
// declaration forms already refused at the lowering; the ASSIGNMENT
// forms — the package-level `var a, b any = any(nil).(bool)` (fabricated
// as an assignment by the init lowering) and the local `a, b = x.(bool)`
// — stored the component RAW into the interface cell, and the refusal
// only fired downstream at the first interface equality. Both now refuse
// AT THE LOWERING with the same named cause. RED BY DESIGN: gc runs both
// fine (the expected column records the oracle's truth) — a standing
// frontend-refuses/gc-succeeds coverage red, never a wrong answer,
// retiring when the interfaces campaign lands the tuple-component boxing.

// The issue53619 shape, verbatim: package-level, interface-typed,
// comma-ok on a nil interface.
var c = b
var d = a

var a, b any = any(nil).(bool)

func globalCommaOkIntoInterface() int {
	if c != false {
		panic("c")
	}
	if d != false {
		panic("d")
	}
	return 1
}

// The local ASSIGNMENT form (declared interfaces, then `=`).
func localAssignCommaOkIntoInterface() int {
	var x any = 7
	var v, ok any
	v, ok = x.(int)
	if v != 7 || ok != true {
		panic("local")
	}
	return 1
}
