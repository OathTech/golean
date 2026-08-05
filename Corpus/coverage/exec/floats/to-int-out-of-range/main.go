package main

// EXPECTED-UNSUPPORTED negative pins (floats design note 2026-08-04
// §3.3, decision 4): a non-constant float -> int conversion whose value
// is out of the target's range (or NaN) is IMPLEMENTATION-DEPENDENT in
// Go — amd64 CVTTSD2SI yields 1<<63, arm64 FCVTZS saturates, NaN
// differs likewise — so GoCore refuses it at runtime with an explicit
// `.unsupported` rather than model any one platform's value. Go runs
// both subjects to completion (expected_status ok); the Lean side stays
// PERMANENTLY red at lean-observation with status `unsupported` — that
// red IS the pin on the refusal. Recorded in the baseline header and in
// baselines/untriaged-count (a deliberate fail-closed refusal, not an
// untriaged fidelity bug). The observed return value is a constant on
// purpose: the platform-dependent converted value must not enter the
// observation.
func floatToIntOutOfRange() int {
	f := 1e30 // far above int64's range; the conversion below is runtime
	n := int64(f)
	_ = n // evaluated, discarded: the conversion itself is the subject
	return 3
}

func floatToIntNaN() int {
	zero := 0.0
	nan := zero / zero
	n := int64(nan)
	_ = n
	return 7
}

func main() {
	floatToIntOutOfRange()
	floatToIntNaN()
}
