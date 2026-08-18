package main

// Multi-package guardrail (raft W1.1, 2026-08-18): the DIAMOND import.
// `left` and `right` both import `base`; main imports all three. The
// spec (§Program initialization) initializes every package exactly
// ONCE, dependencies first — so base's package var (whose initializer
// counts its own executions) is initialized a single time and both
// arms see the SAME base state. A naive per-import re-lowering or
// re-initialization would double base.Inits and skew every sum.

import (
	"base"
	"left"
	"right"
)

func diamondImport() int {
	// base.Seed = 10 (computed once: Inits must be 1).
	// left.L = base.Seed + 1 = 11; right.R = base.Seed + 2 = 12.
	return base.Inits*1000 + left.L + right.R
}

func main() {}
