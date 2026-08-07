package main

// A CALL in a short-circuit RHS operand: GoCore has no call
// expressions (calls are statements), so the frontend must hoist the
// call — but hoisting ahead of `&&`/`||` would evaluate an operand Go
// only evaluates conditionally, changing evaluation order. The
// declaration is therefore frontend-quarantined ("call/allocation in
// short-circuit operand") and this case is a TRACKED red at stage
// frontend-export: a known native-frontend coverage gap made visible
// as a corpus pin (grossmith findings §3,
// docs/2026-08-07_grossmith-findings.md), so its eventual closure is
// a deliberate baseline move instead of an invisible non-case.

func bump(counter *int) bool {
	*counter++
	return *counter > 0
}

func shortCircuitCallOperand() int {
	calls := 0
	// RHS call must NOT run: false && f().
	if false && bump(&calls) {
		return -1
	}
	// RHS call must run exactly once: true && f().
	if true && bump(&calls) {
		return calls
	}
	return -2
}

func main() {
	shortCircuitCallOperand()
}
