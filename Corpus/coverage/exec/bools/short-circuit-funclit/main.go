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


// ---------------------------------------------------------------------
// FIX ROUND #2 (2026-08-16) — the E6 INTERACTION, and the shapes the C1
// fix newly ADMITTED.
//
// The C1 fix (emitFuncLit saves/restores hoistForbidden/scHoistOK) does
// not only stop over-refusing `make`/`append`. It also restores the
// literal body to the SAME emitter configuration it has outside a
// short-circuit — and one of the things that configuration controls is
// the E6 / BUG-032 gate (`docs/2026-08-11_latitude-inventory.md` §E6,
// emit.go:6355 `if e.fnHasRecv && e.hoistForbidden == ""`).
//
// Before the fix that gate could not fire inside a literal-in-SC,
// because hoistForbidden was non-empty there. So a receive-bearing
// literal with a potentially-panicking len/cap operand SKIPPED the
// fail-closed refusal and emitted len INLINE — losing exactly the
// len-vs-receive order the refusal exists to protect. Nesting a literal
// in a short-circuit RHS was a way to walk around a fail-closed guard.
//
// The invariant these rows pin is the intended disposition: THE SAME
// LITERAL BEHAVES IDENTICALLY IN AND OUT OF A SHORT-CIRCUIT. The
// `e6-*` pair must refuse identically (both frontend-export, same
// verbatim BUG-032 reason); the `admit-*` rows must run identically.

// e6RecvLenInSC: receive-bearing literal (the receive is in a dead
// branch, exactly the BUG-032 shape) whose live path evaluates
// `iv.(uint64) + len(b[j])`. Go's spec leaves the type-assertion panic
// and the index panic unordered; gc realizes left to right, so the
// INTERFACE CONVERSION panics. Called in `&&`'s RHS.
func e6RecvLenInSC(n, j uint64) uint64 {
	var iv interface{} = "s"
	b := make([][]uint64, 0)
	ch := make(chan uint64, 1)
	ch <- 1
	r := uint64(0)
	if n > 0 && func() bool {
		if j > 100 {
			return <-ch > 0
		}
		return iv.(uint64)+uint64(len(b[j])) > 0
	}() {
		r = 1
	}
	return r
}

// e6RecvLenOutside: the CONTROL — byte-identical literal body, called
// from a plain statement. This has always refused; the row exists so
// the pair can be compared, not so the control is news.
func e6RecvLenOutside(j uint64) uint64 {
	var iv interface{} = "s"
	b := make([][]uint64, 0)
	ch := make(chan uint64, 1)
	ch <- 1
	f := func() bool {
		if j > 100 {
			return <-ch > 0
		}
		return iv.(uint64)+uint64(len(b[j])) > 0
	}
	if f() {
		return 1
	}
	return 0
}

// admitNewInSC: `new` inside a literal inside `&&`'s RHS. Refused
// before the C1 fix ("new in short-circuit operand"), admitted now.
func admitNewInSC(n, k uint64) uint64 {
	r := uint64(0)
	if n > 0 && func() bool {
		p := new(uint64)
		*p = k + 5
		return *p > k
	}() {
		r = 1
	}
	return r*10 + n
}

// admitCopyInSC: `copy` inside a literal inside `||`'s RHS — evaluated
// exactly when the left operand is false.
func admitCopyInSC(n, k uint64) uint64 {
	got := uint64(0)
	r := uint64(0)
	if n > 0 || func() bool {
		src := []uint64{k, k + 1, k + 2}
		dst := make([]uint64, 2)
		got = uint64(copy(dst, src))
		return dst[1] == k+1
	}() {
		r = 1
	}
	return r*100 + got
}

// admitMapLitInSC: a map COMPOSITE LITERAL inside a literal inside
// `&&`'s RHS. Composite literals were part of the same over-refusal.
func admitMapLitInSC(n, k uint64) uint64 {
	r := uint64(0)
	if n > 0 && func() bool {
		m := map[uint64]uint64{1: k, 2: k + 1}
		return m[2] == k+1
	}() {
		r = 1
	}
	return r*1000 + k
}

func main() {
	litInSCAnd(1, 3)
	litInSCOr(0, 2)
	litInSCCapture(2, 3)
	outsideCallLit(4)
	outsideThenSC(1, 5)
	admitNewInSC(1, 4)
	admitCopyInSC(0, 5)
	admitMapLitInSC(1, 7)
	admitSplatInLitInSC(1, 2)
	admitElidedInLitInSC(1, 2)
	// e6RecvLenInSC / e6RecvLenOutside are NOT called here: both panic
	// on every live argument, and main() is compiled and run by tooling
	// that expects a clean exit. The differential driver calls them.
	_ = e6RecvLenInSC
	_ = e6RecvLenOutside
}

// --- the two hoistForbidden readers the C1 round did not probe -------
//
// C1's fail-closed-remainder probe covered nine shapes placed DIRECTLY
// in a short-circuit RHS. Two readers of `hoistForbidden` were not in
// that set: `splatMultiCall` (emit.go:1595, tuple forwarding) and the
// ELIDED `&composite` arm (emit.go:4921). Probed in fix round #2
// through both emitters; verbatim results in g2.md. Both keep their
// refusal in the DIRECT position, byte-identical before and after, and
// both are admitted inside a literal — which is the fix's intent. The
// two rows below pin the admitted half; the direct half is unchanged
// and already covered by the standing short-circuit refusal record.

type scBox struct{ v uint64 }

func scTwo(k uint64) (uint64, uint64) { return k, k + 1 }

func scSum2(a, b uint64) uint64 { return a + b }

// admitSplatInLitInSC: tuple forwarding `scSum2(scTwo(k))` — the
// splatMultiCall reader — inside a literal inside `&&`'s RHS.
func admitSplatInLitInSC(n, k uint64) uint64 {
	got := uint64(0)
	r := uint64(0)
	if n > 0 && func() bool {
		got = scSum2(scTwo(k))
		return got > k
	}() {
		r = 1
	}
	return r*10000 + got
}

// admitElidedInLitInSC: an ELIDED `&composite` (`[]*scBox{{k}, {k+1}}`
// — the elements elide the `&scBox`) inside a literal inside `&&`'s RHS.
func admitElidedInLitInSC(n, k uint64) uint64 {
	got := uint64(0)
	r := uint64(0)
	if n > 0 && func() bool {
		ps := []*scBox{{k}, {k + 1}}
		got = ps[0].v + ps[1].v
		return got == 2*k+1
	}() {
		r = 1
	}
	return r*10000 + got
}
