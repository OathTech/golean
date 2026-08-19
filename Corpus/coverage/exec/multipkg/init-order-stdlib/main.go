package main

// Multi-package guardrail (raft W1.1 audit F1, 2026-08-18): the
// program initialization list ranges over ALL packages of the complete
// program — the STDLIB ones included — not just the packages we model.
//
// spec#Program_initialization: "Given the list of all packages, sorted
// by import path, in each step the first uninitialized package in the
// list for which all imported packages (if any) are already
// initialized is initialized." spec#Program_execution defines the
// complete program as main "with all the packages it imports,
// transitively" — so `sync` and its own transitive imports are IN the
// list and occupy positions in it.
//
// Here `aaa` sorts BEFORE `bbb`, and both are ready with respect to
// the packages we model (`rec`). A local-only list therefore schedules
// aaa first and observes 12. The real schedule does not: aaa also
// imports `sync`, which cannot be initialized before `rec` (rec is
// ready from step one and "rec" < "sync", so rec always wins that
// step), so at the step after rec only `bbb` is ready among {aaa,
// bbb} — bbb goes first and the observed schedule is 21.
//
// This is the omission-resistant complement to `multipkg/init-order`,
// which pins the same rule over local packages only (and whose
// expectation is correct as written: it imports no stdlib).

import (
	"aaa"
	"bbb"
	"rec"
)

// initStdlibSeq is the observed schedule: 21, NOT 12.
func initStdlibSeq() int {
	return rec.Seq
}

// initStdlibMarks pins the same fact through the push counts: aaa
// initialized second (A=2), bbb first (B=1).
func initStdlibMarks() int {
	return aaa.A*100 + bbb.B
}

func main() {}
