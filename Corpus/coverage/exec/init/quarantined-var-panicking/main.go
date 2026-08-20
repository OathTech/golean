package main

// F1b guardrail (audit fix round, raft W4.0 2026-08-20): the
// effect-isolation predicate must not admit an initializer that can
// PANIC. Effect-freedom and panic-freedom are different properties;
// H-11's first cut checked only the first, so this program exported
// cleanly and RAN — the machine printing 3 where go run dies in
// package initialization. A skipped panic is a silent wrong answer,
// not a visible divergence.
//
// The shape: os.Getenv IS on the pure-callee allowlist, so the call is
// admissible; the second element of the composite is a slice-to-array
// conversion of a length-2 slice to [4]int, which panics at init. The
// predicate now walks a POSITIVE list of panic-free expression shapes
// and refuses array-target conversions (the only conversion class that
// can panic), so the whole export refuses.
//
// The sibling subject touches nothing, so the pin is two-sided: correct
// = FAIL at frontend-export; re-opened = the export succeeds, the
// machine runs to completion, and the row fails at the go-observation
// stage instead (go panicked, the machine did not). Stage movement is
// tracked-baseline drift.

import "os"

var quarPanicSlice = []int{1, 2}

var quarPanicBad = [2]any{os.Getenv("GOLEAN_H11_NEVER_SET"), [4]int(quarPanicSlice)}

var quarPanicGood = 3

func quarPanicSibling() int { return quarPanicGood }

func main() { println(quarPanicSibling(), len(quarPanicBad)) }
