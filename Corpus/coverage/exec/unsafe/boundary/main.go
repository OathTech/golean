package main

import "unsafe"

// OUT-OF-LANGUAGE BOUNDARY MARKERS (slice 6, the whole-language bar):
// spec#Package_unsafe. The ledger classifies Package_unsafe
// out-of-language — the spec's own guard ("packages using unsafe must
// be vetted manually … may be non-portable", and the whole section is
// gated on implementation-specific layout), and modeling its
// observables means modeling gc's memory layout, the doctrine's exact
// anti-goal. These two rows exist so the boundary is a VISIBLE RED,
// never grey: marker-only, justification logged in the ledger row
// (the charter's anticipated rare marker-only case).
//
// sizeof-const picks the one corner the spec DOES force
// (spec#Size_and_alignment_guarantees fixes the byte sizes of the
// fixed-width types) — and it is GREEN, measured at landing: the whole
// expression is a CONSTANT, folded by go/constant at the frontend
// before any unsafe machinery could be consulted (the S3
// delegated-constant caveat, working in the honest direction — the
// folded value is spec-forced, so the green attests go/types'
// spec-conformant fold, never a layout model). pointer-roundtrip is
// the type-safety escape itself (unsafe.Pointer rule 1) — the RED
// boundary row that must never pass by accident; refusal:
// "basic type unsafe.Pointer" (wire.go).

func unsafeSizeofConst() int {
	return int(unsafe.Sizeof(int64(0)))*10 + int(unsafe.Sizeof(int32(0))) // 84
}

func unsafePointerRoundtrip() int {
	x := 7
	p := unsafe.Pointer(&x)
	q := (*int)(p)
	return *q // 7
}

func main() {
	unsafeSizeofConst()
	unsafePointerRoundtrip()
}
