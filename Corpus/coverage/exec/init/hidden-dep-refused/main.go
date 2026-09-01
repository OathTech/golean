package main

// E7 DETECTOR PIN (t1-fidelity-fixes, 2026-08-31): the fail-closed
// hidden-dependency-shape detector the E7 charter-era ruling ordered
// ("ships FIRST"; docs/2026-08-11_latitude-inventory.md §E7). A
// package-level initializer whose evaluation reaches a method call
// THROUGH AN INTERFACE, where a same-package method of that name reads
// an initialized package variable, has a hidden data dependency the
// reference analysis cannot see — spec#Package_initialization makes
// the order UNSPECIFIED there, and the realized go/types InitOrder is
// KNOWN ≠ gc on exactly this shape (the init/hidden-dep-order
// deviation pin). The frontend REFUSES the export naming the cause
// (tools/nativefrontend/hiddendep.go); only the recorded deviation
// case lowers, under the apparatus-side explicit allow
// (--allow-hidden-dep-init-order, keyed to that case id in
// scripts/diff-coverage + scripts/check-frontend-pins).
//
// This row is RED (frontend-export) BY DESIGN — the refusal firing IS
// the pin. gc @ go1.26.5 runs it fine: 21103 (hdA before hdB, so
// v() = 21; probed .tmp-era t1 fix round). The shape is one indirection
// deeper than the deviation pin's (the interface call sits in a helper
// FUNCTION the initializer calls, exercising the detector's
// reachability walk, not just its root scan).

type opI interface{ v() int }

type opT struct{}

var hdA = 3
var hdB = hdVia() // hidden dependency on hdA through the interface dispatch
var hdC = hdA + 100

func (opT) v() int { return hdA * 7 }

func hdVia() int { return opI(opT{}).v() }

func hiddenDepRefused() int {
	return hdB*1000 + hdC
}

func main() { hiddenDepRefused() }
