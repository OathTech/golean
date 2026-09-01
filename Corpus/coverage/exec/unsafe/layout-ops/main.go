package main

import "unsafe"

// BUG-070 REFUSAL PINS (t1-fidelity-fixes, 2026-08-31): the
// unsafe.Sizeof/Offsetof/Alignof boundary is a MECHANISM now, not a
// curation convention. Pre-fix, these operators passed through
// go/constant at emit time and landed on the wire as anonymous
// literals — gc-amd64's implementation-specific layout
// (spec#Size_and_alignment_guarantees forces only the fixed-width
// types) leaking into the model with no refusal (assessment
// p2-keeps-a2a3bcd §1.1: layoutConst folded to 8248 on amd64, 4164 on
// 386/arm, exported clean). The frontend now refuses the whole export
// on any unsafe.{Sizeof,Offsetof,Alignof} reference
// (checkUnsafeLayoutOps, emit.go) — whole-export because a folded
// layout constant launders through named constants past any per-use
// subtree scan.
//
// BOTH rows are RED (frontend-export) BY DESIGN:
//   sizeof-fixed  — the spec-FORCED corner (int64/int32 sizes), the
//     shape that used to be the boundary case's GREEN row: refused
//     anyway, deliberately — a spec-forcedness carve-out would put a
//     layout-model census inside the frontend for the sake of one
//     attestation row; the fold it attested was go/types', not ours.
//     gc @ go1.26.5: 84.
//   layout-struct — the implementation-specific leak itself (struct
//     size + field offset). gc @ go1.26.5 on amd64: 8248.
// The unsafe.Pointer type-escape keeps its OWN distinct refusal at
// unsafe/boundary (pointer-roundtrip, "basic type unsafe.Pointer").

func unsafeSizeofFixed() int {
	return int(unsafe.Sizeof(int64(0)))*10 + int(unsafe.Sizeof(int32(0))) // gc: 84
}

type layoutS struct {
	a bool
	b int64
	c bool
}

func unsafeLayoutStruct() int {
	return int(unsafe.Sizeof(int(0)))*1000 + int(unsafe.Sizeof(layoutS{}))*10 + int(unsafe.Offsetof(layoutS{}.b)) // gc amd64: 8248
}

func main() {
	unsafeSizeofFixed()
	unsafeLayoutStruct()
}
