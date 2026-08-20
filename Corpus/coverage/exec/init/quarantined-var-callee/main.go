package main

// H-11 boundary pin: an initializer that CALLS a quarantined SOURCE
// function LOWERS (a call node emits fine), so H-11's dry-run never
// fails on it and the var is NOT quarantined — the standing C3 rule
// (checkInitQuarantine: $pkginit's call graph reaching a quarantined
// declaration refuses the WHOLE export) keeps covering it. This is
// deliberate v1 scope: the callee's lowerable parts could have modeled
// effects the machine would otherwise perform, and quarantining the
// var would silently drop them. Every row here stays red at
// frontend-export; a flip means somebody widened H-11 transitively —
// which owes a fresh effect argument, not just this pin's re-pin.

import "os"

func h11Helper() string { return os.Getenv("GOLEAN_H11_CALLEE") }

var viaCall = h11Helper()

var calleeSibling = 7

func quarCalleeSibling() int { return calleeSibling }

func main() { println(quarCalleeSibling()) }
