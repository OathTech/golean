package main

// Multi-package guardrail (raft W1.1, 2026-08-18): the PANIC form of
// the BUG-010 witness. The failed assert between two same-named types
// from different packages panics, and gc's runtime message names this
// exact class verbatim: `interface conversion: interface {} is inner.T,
// not inner.T (types from different packages)` — the qualifier is the
// package NAME (ambiguous on purpose) plus the disambiguating suffix.
// This pins the machine's MESSAGE fidelity for path-keyed TypeIds, not
// just its identity verdict — the identity half lives in
// multipkg/same-name-identity. RED from 2026-08-18 (BUG-059: the machine
// rendered the path-qualified KEY) until 2026-09-05 (lane fr19-bug097,
// design note docs/2026-09-05_fr19-bug097-design.md §3): the wire
// carries gc's DISPLAY (`inner.T`, package `red/inner`) beside the key,
// and the concrete-target text appends gc's suffix when the displays
// collide — `(types from different packages)` for distinct declaring
// paths. GREEN.

import (
	bi "blue/inner"
	ri "red/inner"
)

func sameNameIdentityPanic() int {
	var a any = ri.T{Tag: 1}
	v := a.(bi.T) // panics: types from different packages
	return v.Tag
}

func main() {}

// W4.3 item 5: the R-1 forced-half row, as far as the machine allows.
// The forced half here is: the failed assert PANICS, control flow
// (recover catches it), and the run continues. The payload's KIND
// (a runtime error value) is NOT yet in-language checkable under the
// machine: asserting the recovered value to `error` refuses (the
// runtime error type carries no MethodSetRecord — the BUG-009/BUG-053
// fail-closed class), so the kind clause of the forced half is
// RECORDED AS BLOCKED on that semantic-core surface, not silently
// skipped. The TEXT half's two members are recorded in this file for
// the day the split completes:
//   gc:  interface conversion: interface {} is inner.T, not inner.T
//        (types from different packages)
//   ours: WAS the path-qualified form over red/inner.T / blue/inner.T;
//         since 2026-09-05 byte-equal to gc's (display/identity split —
//         the quotient is no longer needed for this row).
func sameNameForcedHalf() string {
	out := ""
	func() {
		defer func() {
			if r := recover(); r != nil {
				out = "panicked-and-recovered"
				return
			}
			out = "no-panic"
		}()
		var a any = ri.T{Tag: 1}
		v := a.(bi.T)
		_ = v
	}()
	return out
}
