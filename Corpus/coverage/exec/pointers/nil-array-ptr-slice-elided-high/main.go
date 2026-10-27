package main

// The ELIDED-HIGH half of `pointers/nil-array-ptr-slice`'s family, pinned
// at its CURRENT class (holes-arc audit fix round, 2026-08-21, finding
// F1). Slicing an array requires an addressable operand and takes its
// address (spec#Slice_expressions), so `(*ap)[:]` with `ap == nil` is the
// same implicit `&(*ap)` composition as BUG-063's receiver shapes:
// spec#Address_operators' eager panic clause applies and gc PANICS.
// `go run` (go1.26.5) answers 100 — the recovered value — for every
// function below.
//
// The machine's `emitAddressOf` StarExpr collapse hands the slice node a
// nil base; until 2026-10-27 the base-nil arm was not modeled and surfaced
// as an honest STUCK ("expected array or slice value for slice expression,
// got GoValue.nil") — fail closed, never a wrong answer, exactly what the
// sibling row `nil-array-ptr-slice/slice-expr-nil` (explicit high)
// recorded. FIXED 2026-10-27 (BUG-227, lane core/fix-bug227-236-1027):
// applySlice's `.nil` base arm raises gc's recoverable nil dereference
// before any bound is looked at, so the four nil rows below are strict
// PASS rows now, beside the two scope controls.
//
// WHY THESE ROWS EXIST NOW. Two of them (`deref-elided-high`,
// `deref-low-only`) used to answer 100 by ACCIDENT: the pre-BUG-066
// default-high lowering re-emitted the whole operand inside a
// `builtin-len`, and that second emission dereferenced the nil pointer
// and panicked — the right answer for the wrong reason, produced by the
// very double evaluation BUG-066 removed. With the base evaluated ONCE
// and the array's static length used as the default high, the accident
// is gone and the shape converges on the documented hole. Measured, not
// asserted (frontend at 6146b217 vs the fix at 90b12339, same wire
// decoder): `(*ap)[:]` and `(*ap)[1:]` ok/100 -> stuck; `ap[:]` and the
// `*[0]int` form were ALREADY stuck before the fix. So the fix WIDENED a
// fail-closed refusal that was always the machine's real position on
// this base path; it never made a right answer wrong.
//
// The two green rows below were the scope control while the refusal
// stood: a nil pointer reached through a FIELD selector panicked
// correctly on both sides, so the refusal was the slice-base nil arm
// specifically, not a blanket loss of nil handling under the fix. They
// stay as the controls of the arm that now exists.

type nabox struct{ arr [3]int }

func naRecovered(f func() int) int {
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		r = f()
	}()
	return r
}

// Explicit deref, BOTH bounds elided. Was accidentally-correct pre-BUG-066.
func nilDerefElidedHigh() int {
	var ap *[4]int
	return naRecovered(func() int { s := (*ap)[:]; return len(s) })
}

// Explicit deref, nonzero low, elided high. Same accident, same class.
func nilDerefLowOnly() int {
	var ap *[4]int
	return naRecovered(func() int { s := (*ap)[1:]; return len(s) })
}

// Pointer form (implicit deref, `ap[:] ≡ (*ap)[:]`). Stuck before the fix too.
func nilPointerFormElidedHigh() int {
	var ap *[4]int
	return naRecovered(func() int { s := ap[:]; return len(s) })
}

// Zero-length array: the default high is the constant 0, and the base is
// still nil, so the refusal is about the BASE and not the bound. gc still
// panics (the deref happens regardless of the length).
func nilZeroLengthArrayElidedHigh() int {
	var ap *[0]int
	return naRecovered(func() int { s := ap[:]; return len(s) + 7 })
}

// Scope control (green): array FIELD through a nil struct pointer. The
// field-address path has its own nil arm, so the machine panics where gc
// panics — the refusal above is the slice-base arm, nothing wider.
func nilFieldArrayElidedHigh() int {
	var b *nabox
	return naRecovered(func() int { s := b.arr[:]; return len(s)*10 + s[0] })
}

// Scope control (green): the BUG-066 guardrail's own shape
// (`pf().arr[:]`, an array field through a pointer-returning call) with
// the call returning nil.
func nilCallFieldArrayElidedHigh() int {
	pf := func() *nabox { return nil }
	return naRecovered(func() int { s := pf().arr[:]; return len(s) })
}

func main() {
	println(nilDerefElidedHigh())
}
