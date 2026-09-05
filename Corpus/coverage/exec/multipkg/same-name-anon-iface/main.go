package main

// BUG-097 witness (bug095-096 audit fix round, 2026-09-05): the
// ANONYMOUS-interface wire name is qualified with package NAMES
// (`types.TypeString(iface, p.Name())` in emitType / ifaceWireName)
// while every other TypeId is keyed by import PATH (pkgQualifier,
// BUG-010). Two source packages share the NAME `inner` at DISTINCT
// paths (`red/inner`, `blue/inner`); each declares its own T and an
// anonymous `interface{ Get() T }`. Go keys identity on the path, so
// red's value does NOT satisfy blue's interface (`1 4 true false`). A
// name-qualified wire fuses the two interfaces onto ONE wire name: on
// main that was a WRONG ANSWER (whichever registration came last won —
// `1 4 false false`); since BUG-095's noteInterface conflict guard it
// is a REFUSAL by name (`interface wire name registered with two
// different method sets: interface{Get() inner.T} (...red/inner.T vs
// ...blue/inner.T)`). RED until the qualifier is the import path.

import (
	bi "blue/inner"
	ri "red/inner"
)

func sameNameAnonIface() (int, int, bool, bool) {
	x := ri.Make(1)
	y := bi.Make(4)
	return int(x.Get()), int(y.Get()), ri.Is(x), ri.Is(y)
}

func main() {}
