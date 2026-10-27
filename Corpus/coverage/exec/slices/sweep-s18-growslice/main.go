package main

// S18 sweep — the append spill's HEAP regime at the size-class, threshold, header, page,
// division and zero-size arms of gc's growslice (runtime/slice.go growslice/nextslicecap,
// msize.go roundupsize @ go1.26.5): one element appended to a FULL heap-resident slice
// (oldLen > 0, so neither the 32-byte stack buffer nor the growsliceBuf ladder applies),
// cap observed. gc realizes ONE point per cell and the machine's empty tape realizes the
// same point (gcGrowsliceCap, slot 0 — default=gc); the envelope [newLen, max(32, 2·growth)]
// is version-tracked by members=. Each row is the CHEAPEST witness of its arm: a membership
// row's oracle draws are compared against the enumerated members one process at a time, so
// the envelope is kept under ~50 members (the 256 threshold's 1.25x walk needs ≥ 384 and is
// probe-only; its points 287/607/1023/848 are the kernel-checked examples in Ops.lean).
// Probe-verified 2026-10-27 over 700 (kind, capacity) cells (35 element kinds × 20 capacity
// classes): gc plain = gc -race = slot 0 on every cell.
import "sync"

type M64 struct {
	m sync.Mutex
	a [7]int
}

// gc 23 at (11 -> 12): a 24-byte POINTERFUL element crossing 512 bytes: nextslicecap 22, 22·24 = 528 + the 8-byte malloc header → class 576 − 8 = 568 / 24 (the noscan twin gets 24)
func byteSlice11() int {
	s := make([][]byte, 11, 11)
	var z []byte = nil
	s = append(s, z)
	return cap(s)
}

// gc 24 at (11 -> 12): the noscan twin of byteslice-11-12: 528 bytes → class 576 / 24, no header
func arr3int11() int {
	s := make([][3]int, 11, 11)
	var z [3]int = [3]int{}
	s = append(s, z)
	return cap(s)
}

// gc 16 at (8 -> 9): a 64-byte struct holding a sync.Mutex is NOSCAN (tyHasPointersTy .sync → false; gc: a Mutex is two integer words) and 64 bytes (tySizeAlign .sync .mutex = 8): 16·64 = 1024, a class, no header (a pointerful twin would get 1032 → class 1152 − 8 → 17)
func m64x8() int {
	s := make([]M64, 8, 8)
	var z M64 = M64{}
	s = append(s, z)
	return cap(s)
}

// gc 32 at (15 -> 16): a 6-byte element (gc's general division branch) where the rounding shows: nextslicecap 30, 30·6 = 180 → class 192 / 6 = 32
func arr3int16x15() int {
	s := make([][3]int16, 15, 15)
	var z [3]int16 = [3]int16{}
	s = append(s, z)
	return cap(s)
}

// gc 40 at (17 -> 18): the PAGE path: nextslicecap 34, 34·1024 = 34816 > 32760 bytes → rounded to 40960 (5 pages) / 1024
func arr128int17() int {
	s := make([][128]int, 17, 17)
	var z [128]int = [128]int{}
	s = append(s, z)
	return cap(s)
}
