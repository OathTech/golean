package main

// NON-TARGET edges for the `slices.Sort` extern, so green means "the
// capability works", not "the target works" (standing corpus-balance check,
// docs/2026-07-30_quorum-pilot-arc.md; pre-merge audit 2026-07-31, finding
// 12). The target's own shape is pinned by `slices/slices-sort`; nothing
// here is quorum-shaped.
//
// The load-bearing one is `sortUnsignedAboveHalf`: `sortSlice` compares the
// NORMALIZED Lean `Int`, which is non-negative for unsigned kinds, and that
// is the ONLY reason unsigned order is exact. A comparator regressed to a
// two's-complement 64-bit word compare still sorts the signed case
// correctly and silently breaks this one — the domain a raft log index
// actually reaches.

import "slices"

// A nil slice: nothing to sort, no backing cell to touch.
func sortNilSlice() int {
	var xs []int
	slices.Sort(xs)
	return len(xs)
}

// An empty but non-nil slice.
func sortEmptySlice() int {
	xs := []int{}
	slices.Sort(xs)
	return len(xs)
}

func sortSingleElement() int {
	xs := []int{42}
	slices.Sort(xs)
	return xs[0]
}

func sortAlreadySorted() int {
	xs := []int{1, 2, 3, 4}
	slices.Sort(xs)
	return xs[0]*1000 + xs[1]*100 + xs[2]*10 + xs[3]
}

func sortReverseSorted() int {
	xs := []int{4, 3, 2, 1}
	slices.Sort(xs)
	return xs[0]*1000 + xs[1]*100 + xs[2]*10 + xs[3]
}

// A DEFINED integer element type: identity-bearing, sorted through its
// underlying.
type sortIndex uint64

func sortDefinedElemType() uint64 {
	xs := []sortIndex{3, 1, 2}
	slices.Sort(xs)
	return uint64(xs[0])*100 + uint64(xs[1])*10 + uint64(xs[2])
}

// Unsigned ordering ABOVE 2^63 — MaxUint64 must sort LAST, not first.
func sortUnsignedAboveHalf() int {
	const maxU = ^uint64(0)
	const half = uint64(1) << 63
	xs := []uint64{maxU, 1, half, 0}
	slices.Sort(xs)
	n := 0
	if xs[0] == 0 {
		n += 1000
	}
	if xs[1] == 1 {
		n += 100
	}
	if xs[2] == half {
		n += 10
	}
	if xs[3] == maxU {
		n++
	}
	return n
}

// Signed ordering BELOW zero — negatives must sort first.
func sortSignedNegatives() int {
	xs := []int64{3, -9223372036854775808, -1, 0}
	slices.Sort(xs)
	n := 0
	if xs[0] == -9223372036854775808 {
		n += 100
	}
	if xs[1] == -1 {
		n += 10
	}
	if xs[3] == 3 {
		n++
	}
	return n
}

// Sorting a SUB-slice mutates the parent's backing array in place, and
// only the sorted window moves.
func sortSubsliceAliasing() int {
	parent := []int{9, 3, 1, 2, 8}
	slices.Sort(parent[1:4])
	return parent[0]*10000 + parent[1]*1000 + parent[2]*100 + parent[3]*10 + parent[4]
}
