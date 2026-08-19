package main

// Multi-package guardrail (raft W1.1 delta-review F1, 2026-08-18): the
// packages gc SCHEDULES are a PRUNED subset of the spec's "list of all
// packages", and the pruning is OBSERVABLE in the order the surviving
// packages initialize in.
//
// spec#Program_initialization states the schedule over the complete
// program's package list: "Given the list of all packages, sorted by
// import path, in each step the first uninitialized package in the
// list for which all imported packages (if any) are already
// initialized is initialized." Read literally, EVERY package of the
// complete program occupies a position in that list.
//
// gc does not schedule every package. cmd/compile emits a `..inittask`
// record for a package only if the package has residual initialization
// WORK — a non-empty `init` function, or a variable initializer that
// cmd/compile/internal/staticinit could not fold into the data section
// — or an import that itself bears an inittask (deps/go/src/cmd/
// compile/internal/pkginit/init.go, MakeTask: `if len(deps) == 0 &&
// len(fns) == 0 && path != "main" && path != "runtime" { return }`).
// cmd/link then orders exactly the emitted records (deps/go/src/cmd/
// link/internal/ld/inittask.go). A package with no residual work is
// therefore NOT A NODE, and the packages that import it are ready one
// step earlier than the literal reading predicts.
//
// The two subjects are a matched pair over the SAME shape, differing
// only in whether the gating package's initialization is statically
// foldable:
//
//   - `sm` imports `zst`, whose only work is `var X = 5` — a constant,
//     folded into the data section, so `zst` emits no inittask and
//     `sm` is ready at step one. `sm` sorts before `sn`, so `sm`
//     records first:                                 rec.S == 12.
//
//   - `dm` imports `zdy`, whose `init()` assigns at run time, so `zdy`
//     IS a node and `dm` must wait for it. `dn` is ready at step one
//     and records first, `dm` follows once `zdy` has run:
//                                                    rec.D == 21.
//
// A model that schedules every package (no pruning) gets the DYNAMIC
// subject right by accident and the STATIC one wrong: with `zst` in
// the list, `sm` waits for it, `sn` goes first, and the model reports
// 21 for both. The pair is what separates "we implement pruning" from
// "we happen to agree here" — the dynamic subject is the control.
//
// `rec` itself is pruned too (uninitialized package-scope variables
// and functions are no work at all), which is why its own position in
// the list never gates anything here.

import (
	_ "dm"
	_ "dn"
	"rec"
	_ "sm"
	_ "sn"
)

// prunedStaticSeq is 12 — the statically-initialized `zst` is NOT a
// node, so `sm` is ready at step one and beats `sn` on sort order.
func prunedStaticSeq() int {
	return rec.S
}

// prunedDynamicSeq is 21 — the CONTROL. `zdy` does run-time work, so
// it IS a node, `dm` waits for it, and `dn` records first.
func prunedDynamicSeq() int {
	return rec.D
}

func main() {}
