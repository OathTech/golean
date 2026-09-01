package main

// STDLIB FUNCTION-VALUE REFUSAL PINS (t1-fidelity-fixes, 2026-08-31;
// assessment p2-keeps-a2a3bcd §1.3 instance 1 / A3-S7 claim (iv)).
// The E5 stdlib-shim policy admits only the direct CALL shape
// (`strings.Fields(x)`); the function VALUE (`f := strings.Fields`)
// has always been refused — but the refusal named a PHANTOM cause
// ("field selector on anonymous struct type invalid type": the
// selector fell through to the FIELD-selection machinery, and
// goTypeOf of a package name is the invalid type). The charter
// requires a refusal that NAMES ITS CAUSE at the point of failure;
// emitSelector now intercepts stdlib-package-qualified selectors in
// value position and says what actually happened (emit.go,
// t1-fidelity-fixes).
//
// BOTH rows RED (frontend-export) BY DESIGN — the boundary is
// unchanged, only its name is honest now; the rows pin the messages:
//   shimmed-value   — an ALLOWLISTED member as a value ("used as a
//     function VALUE: the stdlib shim admits only the direct-call
//     shape").
//   unmodeled-value — a NON-allowlisted member as a value
//     ("stdlib-qualified selector ... in value position ... outside
//     the modeled surface").
// gc @ go1.26.5 runs both fine (probed, t1 fix round): 3 / true.

import "strings"

func shimmedValue() int {
	f := strings.Fields // allowlisted member, VALUE shape: refused by name
	return len(f("a b c")) // gc: 3
}

func unmodeledValue() bool {
	f := strings.Contains // unmodeled member, VALUE shape: refused by name
	return f("ab", "a") // gc: true
}

func main() {
	shimmedValue()
	unmodeledValue()
}
