// The dot-imported float-bits call (TestCalibrationAgainstWire): since FR-36
// (2026-10-06) the frontend lowers it to the SAME `float-bits` primitive as
// the qualified spelling (tools/nativefrontend/dotimport.go
// emitPrimitiveCall — one object-keyed lookup for both spellings). Until then
// it refused by name (audit fix round D, 2026-09-05; cause
// dot-import-float-bits, retired with the lowering).
package main

import . "math"

func fbDot(f float64) uint64 { return Float64bits(f) }
