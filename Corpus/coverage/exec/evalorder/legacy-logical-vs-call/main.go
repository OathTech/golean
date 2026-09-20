package main

// BUG-113 — the LEGACY (non-pilot) evaluation-order path evaluates a binary
// LOGICAL operation AFTER a lexically later call in the same statement
// (evaluation-order model v2.1; found by the Stage C adversarial audit
// docs/2026-09-20_unseq-stage-c-audit.md F1, programs c01/c02 verbatim).
// spec#Order_of_evaluation: «all function calls, method calls, receive
// operations, and binary logical operations are evaluated in lexical
// left-to-right order» — `left || b` is lexically before `change()`, so the
// `||` must read b BEFORE change() sets it: gc prints `logical false 0` (plain
// and -N -l). The legacy ANF hoist (tools/nativefrontend/emit.go) lifts the
// call to a temp BEFORE the statement and leaves the `||` inline in the
// residual, so the machine reads the post-call b: `logical true 0` — a WRONG
// ANSWER, pre-existing on main 6a7beb3d (main = candidate here). The operand
// `left` is a PACKAGE variable, outside the pilot grammar, so the sweep stays
// on the legacy path by name («package-level variable»); the pilot's own row
// `evalorder/unseq-pilot/r2b` (a private `left`) is the same sweep lowered as
// an `unseq` graph and answers gc's `logical false 0` — that is exactly why
// r2b's born strict observation differs from main's legacy default (audit F5).
// Fix: Stage E's migration of the `&&`/`||` sweeps to `unseq` (or the E1
// completion anchoring in the legacy hoister); not fixed here — rowed.

var left = false
var leftT = true

func sinkL(b bool, n int) { println("logical", b, n) }
func sinkR(n int, b bool) { println("logical", n, b) }

// c01: `sinkL(left || b, change())` — gc `logical false 0`; the machine (legacy)
// `logical true 0`. FAIL/differential, on BUG-113's Cases line.
func orVsCall() int {
	b := false
	change := func() int { b = true; return 0 }
	sinkL(left || b, change())
	return 1
}

// c02-and: `sinkL(leftT && b, change())` — the `&&` spelling; gc `logical false 0`;
// the machine `logical true 0`. FAIL/differential, on BUG-113's Cases line.
func andVsCall() int {
	b := false
	change := func() int { b = true; return 0 }
	sinkL(leftT && b, change())
	return 1
}

// c02-callfirst: `sinkR(change(), left || b)` — the call is lexically FIRST, so
// the spec orders it before the `||`: gc and the machine agree, `logical 0 true`.
// The must-stay-green control.
func callFirstControl() int {
	b := false
	change := func() int { b = true; return 0 }
	sinkR(change(), left || b)
	return 1
}

func main() {
	orVsCall()
	andVsCall()
	callFirstControl()
}
