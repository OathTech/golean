package main

// Multi-package guardrail (raft W1.1, 2026-08-18): the PANIC form of
// the BUG-010 witness. The failed assert between two same-named types
// from different packages panics, and gc's runtime message names this
// exact class verbatim: `interface conversion: interface {} is inner.T,
// not inner.T (types from different packages)` — the qualifier is the
// package NAME (ambiguous on purpose) plus the disambiguating suffix.
// This pins the machine's MESSAGE fidelity for path-keyed TypeIds, not
// just its identity verdict — the identity half lives in
// multipkg/same-name-identity.

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
