package main

// Guardrails for the CLOSURE QUARANTINE LEAK (post-autonomy audit
// finding R2A-F2, 2026-08-16): `emitFuncLit` emits a function
// literal's BODY without saving/restoring the `hoistForbidden` /
// `scHoistOK` flags, so a literal that appears inside a short-circuit
// RHS emits its own statements under "short-circuit operand" and any
// `make` / `append` / composite inside it is refused.
//
// That refusal is an OVER-refusal. The literal's body becomes its own
// lifted function: its statements are not in the caller's statement
// stream at all, so there is nothing to hoist out of the conditional
// and no evaluation order to change. The hoist restriction belongs to
// the ENCLOSING statement context, not to a nested function body.
//
// The rows below are committed RED (stage frontend-export, reason
// `make in short-circuit operand` / `append in short-circuit
// operand`) before the fix, per guardrails-first; the `outside-*`
// controls carry the SAME literal body outside any short-circuit and
// PASS today, so a flip in them would mean the fix widened something
// it should not have.
//
// go run is the oracle for every row: the values below are Go's.

// buildLen: the literal body under test — an allocation (`make`), a
// growth loop (`append`) and a length readout, with nothing captured.
// Used verbatim in and out of the short-circuit position.
func buildLen(k uint64) uint64 {
	s := make([]uint64, 0, 1)
	for i := uint64(0); i < k; i++ {
		s = append(s, i)
	}
	return uint64(len(s))
}

// litInSCAnd: the leak witness. The func literal is CALLED in the
// right operand of `&&`, so its body emits under hoistForbidden. Go
// evaluates the literal exactly when the left operand does not decide
// the result — the returned count pins that.
func litInSCAnd(n, k uint64) uint64 {
	calls := uint64(0)
	r := uint64(0)
	if n > 0 && func() bool {
		calls++
		s := make([]uint64, 0, 1)
		for i := uint64(0); i < k; i++ {
			s = append(s, i)
		}
		return uint64(len(s)) == k
	}() {
		r = 1
	}
	return r*100 + calls
}

// litInSCOr: the same, on `||`'s right operand — evaluated exactly
// when the left operand is false.
func litInSCOr(n, k uint64) uint64 {
	calls := uint64(0)
	r := uint64(0)
	if n > 0 || func() bool {
		calls++
		s := make([]uint64, 0, 1)
		for i := uint64(0); i < k; i++ {
			s = append(s, i)
		}
		return uint64(len(s)) > 0
	}() {
		r = 1
	}
	return r*100 + calls
}

// litInSCCapture: the literal captures an enclosing variable AND
// allocates, so the capture path and the hoist flags interact.
func litInSCCapture(n, k uint64) uint64 {
	total := uint64(0)
	r := uint64(0)
	if n > 0 && func() bool {
		s := make([]uint64, 0, 1)
		for i := uint64(0); i < k; i++ {
			s = append(s, i+n)
		}
		for _, v := range s {
			total += v
		}
		return true
	}() {
		r = 1
	}
	return r*1000 + total
}

// outsideCallLit: the CONTROL — the identical literal body, called
// from a plain statement. PASS today; must stay PASS.
func outsideCallLit(k uint64) uint64 {
	f := func() uint64 {
		s := make([]uint64, 0, 1)
		for i := uint64(0); i < k; i++ {
			s = append(s, i)
		}
		return uint64(len(s))
	}
	return f()
}

// outsideThenSC: the control body runs BEFORE a short-circuit that
// contains no literal, so the two mechanisms meet in one function
// without nesting.
func outsideThenSC(n, k uint64) uint64 {
	m := buildLen(k)
	r := uint64(0)
	if n > 0 && m == k {
		r = 1
	}
	return r*100 + m
}

func main() {
	litInSCAnd(1, 3)
	litInSCOr(0, 2)
	litInSCCapture(2, 3)
	outsideCallLit(4)
	outsideThenSC(1, 5)
}
