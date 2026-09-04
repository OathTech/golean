package main

// FLIPPED GREEN 2026-09-04 (lane fr4-rowm, memo §3 row M): `slices.Sort`
// at a STRING element type lowers through the real source-through generic
// (`pdqsortOrdered[string]`), so the refusal this row pinned no longer
// exists. History: the row was born a red `frontend-export` guardrail
// (pre-merge audit 2026-07-31, finding 12) when only `slices.Sort` AT
// INTEGER ELEMENTS was modeled — the quorum-pilot `sortSlice` machine op —
// so a silent widening of that surface would show as baseline drift. The
// widening is now deliberate and ruled (the G1-G9 stdlib plan, [USER]
// «(3) agree, go ahead with the plan», relayed); the id is kept so the
// baseline records the FAIL→PASS flip by name. Wider string/float/named-
// kind coverage: `slices/slices-sort-kinds/*`.

import "slices"

func sortNonIntegerElements() int {
	xs := []string{"b", "a", "c"}
	slices.Sort(xs)
	if xs[0] == "a" {
		return 1
	}
	return 0
}
