package main

// Multi-package guardrail (raft W1.1 delta-review F1, 2026-08-18): the
// PRUNING applies to stdlib packages too, and it is what makes a blank
// stdlib import gate nothing.
//
// This is the minimal divergence the 120-seed randomized differential
// harness found (seed 46, artifacts/delta-review-probe/gen2.py): two
// source packages whose only imports are the recorder and ONE blank
// stdlib import each.
//
//	ce imports _ "sync/atomic"
//	sy imports _ "unicode/utf8"
//
// Neither stdlib package has any initialization work — both are pure
// code, no run-time variable initializers, no init functions — so
// cmd/compile emits no `..inittask` for either and cmd/link never sees
// them. They are NOT nodes of the schedule, so they gate nothing:
// `ce` and `sy` are both ready at step one and take symbol order,
//
//	"ce..inittask" < "sy..inittask"  =>  ce first  =>  rec.Seq == 12.
//
// The complement `multipkg/init-order-stdlib` pins the OTHER
// direction with `sync`, which DOES have init work and therefore does
// gate its importer. Together they say: it is not "importing a stdlib
// package" that delays a package, it is importing a stdlib package
// that gc actually schedules.
//
// A model that puts every transitively imported stdlib package in the
// list reports 21 here: it makes `ce` wait for `sync/atomic`'s
// closure and `sy` for `unicode/utf8`'s, and the two closures resolve
// in an order that lets `sy` go first.

import (
	_ "ce"
	"rec"
	_ "sy"
)

// prunedStdlibSeq is 12 — both blank stdlib imports are pruned away,
// so the two packages are ready together and go in symbol order.
func prunedStdlibSeq() int {
	return rec.Seq
}

func main() {}
