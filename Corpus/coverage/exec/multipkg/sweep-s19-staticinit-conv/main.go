package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27 — the CONTROLS of BUG-341 (found by this sweep): a conversion
// that changes the representation (`uint8(zv)`), a float conversion, `int32`
// of an int, and `int64` of a DYNAMIC global are WORK under gc
// (typecheck.Convertop makes them OCONV, or the operand is not static) and
// under the BUG-061 classifier (tools/nativefrontend/staticinit.go,
// conversionInitKind): the gating package keeps its inittask record, its
// importer waits, both sides answer 21. The four same-SimType pairs the
// finding is about — int ≡ int64, uint ≡ uint64 ≡ uintptr on amd64, which gc
// folds — are multipkg/sweep-s19-staticinit-conv-same-class since the fix
// (lane frontend/fix-init-admission-1105, 2026-11-05): refused by name there,
// one package per verdict, since the BUG-061 refusal is whole-export.

import (
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

// The controls: 21 under both.
func uint8OfInt() int     { return rec.S["e"] }
func float64OfInt() int   { return rec.S["f"] }
func int32OfInt() int     { return rec.S["g"] }
func int64OfDynamic() int { return rec.S["h"] }

func main() {
	println(uint8OfInt(), float64OfInt(), int32OfInt(), int64OfDynamic())
}
