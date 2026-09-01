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
// emit time whenever a dyn-fmt shim is injected, an implementor is
// declared in any unit, AND some unit BOXES an implementor into an
// interface outside the fmt-owned operand positions
// (checkFormatterDynHole/walkFormatterBoxing, fmtdesugar.go — the key
// narrowed from implementor-anywhere to boxing reachability,
// 2026-09-01). The key is ENUMERATIVE: the walk's boxing-context list
// in the checkFormatterDynHole header is the named extension point,
// and the formatter-box-* sibling rows pin the contexts the audit
// found missing (range assign, generic body, cross-package).
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
