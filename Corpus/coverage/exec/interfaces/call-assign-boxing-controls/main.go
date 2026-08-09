package main

// Green guards for BUG-051 (closing review 2026-08-09, verifier probes
// b/c/e): the refusal was SPECIFIC to the interface-target-plus-call-RHS
// assignment — these neighbors box (or need no box) correctly, and pin
// that the BUG-051 fix does not disturb them. Separate package from
// interfaces/call-assign-boxing because the red shapes poison their
// whole package's lowering pre-fix.

func mkIntCtl() int { return 11 }

// Probe b control: var-init form boxes correctly.
func callAssignVarInitControl() any {
	var a any = mkIntCtl()
	return a
}

// Probe c control: concrete target, no boxing owed.
func callAssignConcreteControl() int {
	var a int
	a = mkIntCtl()
	return a
}

// Probe e control: per-pair (non-call) assign into interface targets
// boxes at the per-pair site.
func callAssignPerPairControl() any {
	var a, b any
	a, b = 3, 4
	_ = b
	return a
}

func main() {
	callAssignVarInitControl()
	callAssignConcreteControl()
	callAssignPerPairControl()
}
