// FR-36 (2026-10-06): a dot-imported stdlib member resolves through the SAME
// object-keyed binding as the selector spelling (tools/nativefrontend/
// dotimport.go) — the rand-intn primitive LOWERS (dotIntn), a quarantined
// member refuses by name with the package quarantine's text (dotPerm), the
// value shape refuses on FR-14's line (dotIntnValue; the callee of
// dotIntnDefer), and a fmt desugar member refuses naming the desugar
// (dotSprintf — the one named-refusal residual). TestCalibrationAgainstWire
// compares each static verdict with the wire; TestFloatBitsPrimitiveIsSupplied's
// sibling map pins the causes.
package main

import (
	. "fmt"
	. "math/rand"
)

func dotIntn() int                { return Intn(5) }
func dotPerm() int                { return len(Perm(3)) }
func dotIntnValue() func(int) int { return Intn }
func dotIntnDefer()               { defer Intn(5) }
func dotSprintf(x int) string     { return Sprintf("%d", x) }
