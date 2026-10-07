// FR-37 (2026-10-07): a dot-imported package-level VARIABLE of a non-source
// stdlib package refuses by name at the frontend in every shape (read,
// index, assignment target, address-of) with the qualified spelling's
// no-seeded-cell text (tools/nativefrontend/dotimport.go
// refuseDotImportedVar) — judged here as stdlib-var-unmodeled, the selector
// spelling's own cause. Before: the tool judged these lowers(static) and the
// decoder refused the whole wire unnamed. TestCalibrationAgainstWire
// compares each static verdict with the wire; TestFloatBitsPrimitiveIsSupplied's
// map pins the causes.
package main

import . "os"

func dotArgsRead() int     { return len(Args) }
func dotArgsIndex() string { return Args[0] }
func dotArgsAssign()       { Args = nil }
func dotArgsAddr() int     { p := &Args; return len(*p) }
