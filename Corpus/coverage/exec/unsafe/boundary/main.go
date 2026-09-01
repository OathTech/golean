package main

import "unsafe"

// OUT-OF-LANGUAGE BOUNDARY MARKER (slice 6, the whole-language bar;
// re-scoped 2026-08-31, t1-fidelity-fixes/BUG-070):
// spec#Package_unsafe. The ledger classifies Package_unsafe
// out-of-language — the spec's own guard ("packages using unsafe must
// be vetted manually … may be non-portable", and the whole section is
// gated on implementation-specific layout), and modeling its
// observables means modeling gc's memory layout, the doctrine's exact
// anti-goal. This case pins the TYPE-ESCAPE boundary: unsafe.Pointer
// (rule 1) refuses as a wire type — the RED row that must never pass
// by accident; refusal: "basic type unsafe.Pointer" (wire.go).
//
// The sizeof-const row that used to live here (GREEN: a spec-forced
// constant, folded by go/types) moved to unsafe/layout-ops and is RED
// there: since BUG-070 the frontend refuses unsafe.Sizeof/Offsetof/
// Alignof by MECHANISM (checkUnsafeLayoutOps, emit.go), with no
// spec-forcedness carve-out — keeping the fold here would have killed
// this whole export and buried the distinct Pointer-type refusal this
// case exists to pin.

func unsafePointerRoundtrip() int {
	x := 7
	p := unsafe.Pointer(&x)
	q := (*int)(p)
	return *q // 7
}

func main() {
	unsafePointerRoundtrip()
}
