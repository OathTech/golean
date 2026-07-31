package main

// The assert-panic message names the operand's STATIC interface type, not a
// hardcoded `interface {}` (pre-merge audit 2026-07-31, finding 8). Only the
// CONCRETE-target shape prints it; the interface-target shape does not.

type namedIface interface{ P() int }

type namedT struct{ n int }

func (t namedT) P() int { return t.n }

func assertFromNamedInterfaceToPointer() int {
	var i namedIface = namedT{n: 4}
	return i.(*namedT).n
}

func assertFromNamedInterfaceNil() int {
	var i namedIface
	return i.(namedT).n
}
