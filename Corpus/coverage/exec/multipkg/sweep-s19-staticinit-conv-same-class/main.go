package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27; split out of multipkg/sweep-s19-staticinit-conv at BUG-341's
// fix (lane frontend/fix-init-admission-1105, 2026-11-05). The finding: the
// BUG-061 classifier (tools/nativefrontend/staticinit.go, conversionInitKind)
// called a conversion "between distinct basic kinds" WORK, but gc's
// typecheck.Convertop (cmd/compile/internal/typecheck/subr.go, case 4) makes
// a conversion OCONVNOP whenever the two kinds share a types.SimType class —
// on amd64 int ≡ int64 and uint ≡ uint64 ≡ uintptr (types/universe.go) — and
// staticinit then folds `int64(zv)` of a static global exactly as it folds
// `zv` itself: the package gets NO inittask record and its importer runs
// first (gc 12); the frontend, sure it was work, scheduled the importer late
// (21) — a SILENT wrong order. Since the fix the classifier calls the four
// pairs OCONVNOP-shaped (the operand decides: MAYBE-STATIC), and BUG-061's
// guard REFUSES the sensitive order by name (FAIL/frontend-export,
// c-pin/staticinit-uncertain-order, as for `MyInt(zv)`); the expected column
// keeps gc's truth. RED BY DESIGN on BUG-341's Cases line. The controls stay
// in the original package and agree.

import (
	_ "am"
	_ "an"
	_ "bm"
	_ "bn"
	_ "cm"
	_ "cn"
	_ "dm"
	_ "dn"
	"rec"
)

// The four same-SimType pairs: gc 12 (the gating package folded away).
func int64OfInt() int    { return rec.S["a"] }
func uint64OfUint() int  { return rec.S["b"] }
func uintptrOfUint() int { return rec.S["c"] }
func intOfInt64() int    { return rec.S["d"] }

func main() {
	println(int64OfInt(), uint64OfUint(), uintptrOfUint(), intOfInt64())
}
