package main

// Guardrail for the slices.Sort extern (quorum pilot phase 2,
// docs/2026-07-30_quorum-extern-policy.md): CommittedIndex's exact
// shape — an on-stack array sliced and sorted in place, uint64
// elements with duplicates and zeros filled from the right.
import "slices"

func slicesSortUint64() uint64 {
	var stk [7]uint64
	srt := stk[:5]
	srt[4] = 3
	srt[3] = 101
	srt[2] = 3
	srt[1] = 205
	slices.Sort(srt)
	// srt = [0 3 3 101 205]; the n-(n/2+1) position read.
	return srt[5-(5/2+1)]*1000000 + srt[0]*10000 + srt[1]*100 + srt[4]
}

func slicesSortInts() int {
	xs := []int{5, -1, 4, 4, 0}
	slices.Sort(xs)
	return xs[0]*1000 + xs[1]*100 + xs[2]*10 + xs[4]
}
