package main

// Multi-package guardrail (raft W1.1, 2026-08-18): the minimal
// cross-package FUNCTION call. `mathutil` is a source package in the
// case's own directory tree (import path = the subdir's case-relative
// path — the corpus multi-package convention,
// docs/2026-08-18_multipackage-identity.md); the subject calls an
// exported function through the qualified identifier. Pins that a
// cross-package static call resolves to the callee's package-qualified
// FuncId, not a dangling bare name.

import "mathutil"

func crossFuncCall() int {
	return mathutil.Add(2, 3) + mathutil.Double(10)
}

func main() {}
