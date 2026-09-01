package main

import "fmt"

// FORMATTER x DYN-SHIM REFUSAL PIN (t1-fidelity-fixes, 2026-08-31;
// assessment A3-S3 / audit R1-F2's recorded bound): gc consults
// Format ahead of error/Stringer for EVERY verb, but the dynamic fmt
// shim (goleanShimFmtDynVerb) runs inside the model with no
// reflection and cannot see Formatter — pre-fix, a value implementing
// BOTH Formatter and Stringer, boxed through `any` into a dyn site,
// rendered via String where gc calls Format: an `ok` answer differing
// from gc's, the recorded silent-wrong-answer channel of
// stdlibshim.go's dyn bundle. The frontend now refuses the EXPORT at
// emit time whenever a dyn-fmt shim is injected and any declared type
// implements fmt.Formatter (checkFormatterDynHole, fmtdesugar.go).
//
// This row is RED (frontend-export) BY DESIGN — the refusal firing IS
// the pin. gc @ go1.26.5: "via-format" (probed, .tmp-era t1 fix
// round). Static-site Formatter precedence keeps its own distinct
// per-verb refusal pins at fmt/formatter-precedence.

type both int

func (both) Format(s fmt.State, verb rune) { fmt.Fprint(s, "via-format") }
func (both) String() string                { return "via-string" }

func formatterDynBoxed() string {
	var a any = both(3)
	return fmt.Sprint(a) // gc: "via-format" — Format wins at dyn sites too
}

func main() { formatterDynBoxed() }
