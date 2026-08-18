package main

// Multi-package guardrail (raft W1.1, 2026-08-18): cross-package
// INITIALIZATION ORDER (the recorded E7 semantics). Spec §Package
// initialization pins the whole schedule since Go 1.21: sort all
// packages by import path; repeatedly initialize the first
// uninitialized package whose imports are all initialized; within a
// package, variable initializers run before init(). Here `alpha` and
// `beta` (independent of each other, both importing `reclog`) must
// initialize in import-path order — alpha before beta — even though
// main's import declarations name beta FIRST. The digit log pins the
// full schedule: reclog (dependency), alpha's var (1), alpha's init
// (2), beta's init (3).

import (
	"beta"

	"alpha"

	"reclog"
)

func initOrder() int {
	// 123, plus proof both arms linked: alpha.A=1 (first push's count),
	// beta.B=3 (third push's count).
	return reclog.Seq*100 + alpha.A*10 + beta.B
}

func main() {}
