package main

// Single-value CALL assigned into an interface-typed target: `var x I;
// x = f()` with f returning a concrete type. BUG-051 (closing review
// 2026-08-09, verifier probes a/d/f): the assign-site special case kept
// the call in statement position but wrapped the CALL NODE itself, so
// the emitted RHS was to-interface(call) — which NativeToIR refuses
// ("call in expression position is not modeled") — turning ordinary Go
// into a whole-program error (fail-closed OVER-refusal, the
// classification hole class). The refusal poisons the whole package's
// lowering, so the reviewer's green controls (var-init, concrete
// target, per-pair non-call) live in the sibling package
// call-assign-boxing-controls.

type callAssignErr struct{ m string }

func (e callAssignErr) Error() string { return e.m }

func mkInt() int { return 11 }

func makeErr() callAssignErr { return callAssignErr{m: "boom"} }

// Probe a shape (minimal witness): concrete call result into `any`.
func callAssignAny() any {
	var a any
	a = mkInt()
	return a
}

// Probe d shape (the ordinary-Go idiom): concrete error value into an
// `error` variable, then interface dispatch on it.
func callAssignError() string {
	var err error
	err = makeErr()
	return err.Error()
}

// Probe f shape: assignment to an interface-typed NAMED RESULT.
func callAssignNamedResult() (out any) {
	out = mkInt()
	return
}

func main() {
	callAssignAny()
	callAssignError()
	callAssignNamedResult()
}
