package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27 — BUG-341, found by this sweep: the BUG-061 classifier
// (tools/nativefrontend/staticinit.go, conversionInitKind) calls a
// conversion "between distinct basic kinds" WORK, but gc's
// typecheck.Convertop (cmd/compile/internal/typecheck/subr.go, case 4)
// makes a conversion OCONVNOP whenever the two kinds share a
// types.SimType class — on amd64 int ≡ int64 and uint ≡ uint64 ≡ uintptr
// (types/universe.go) — and staticinit then folds `int64(zv)` of a static
// global exactly as it folds `zv` itself. The package gets NO inittask
// record; the frontend, sure it is work, keeps it a node and holds its
// importer back: gc 12, the frontend 21 — a SILENT wrong order, the
// direction the guard cannot see (it enumerates only MAYBE-STATIC
// shapes, and these are classified certain). Four chains pin the four
// same-class pairs, RED at birth; four controls (a representation-changing
// conversion, a float conversion, int32, a dynamic operand) are WORK under
// both and green.

import (
	_ "am"
	_ "an"
	_ "bm"
	_ "bn"
	_ "cm"
	_ "cn"
	_ "dm"
	_ "dn"
	_ "em"
	_ "en"
	_ "fm"
	_ "fn"
	_ "gm"
	_ "gn"
	_ "hm"
	_ "hn"
	"rec"
)

// The four same-SimType pairs: gc 12 (the gating package folded away).
func int64OfInt() int    { return rec.S["a"] }
func uint64OfUint() int  { return rec.S["b"] }
func uintptrOfUint() int { return rec.S["c"] }
func intOfInt64() int    { return rec.S["d"] }

// The controls: 21 under both.
func uint8OfInt() int     { return rec.S["e"] }
func float64OfInt() int   { return rec.S["f"] }
func int32OfInt() int     { return rec.S["g"] }
func int64OfDynamic() int { return rec.S["h"] }

func main() {
	println(int64OfInt(), uint64OfUint(), uintptrOfUint(), intOfInt64(),
		uint8OfInt(), float64OfInt(), int32OfInt(), int64OfDynamic())
}
