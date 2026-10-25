package main

// GREEN since 2026-09-04 (lane fr4-rowm, memo §3 row M) and UNCHANGED by the
// 2026-10-25 re-admission of the `slices.Sort` intercept (backlog row 50,
// lane frontend/g19-sort-intercept-1025): `slices.Sort` at a STRING element
// type lowers through the real source-through generic
// (`pdqsortOrdered[string]`) — the intercept is INTEGER kinds only, and a
// non-integer kind is the generic, NOT a refusal. The id keeps its history:
// the row was born a red `frontend-export` guardrail (pre-merge audit
// 2026-07-31, finding 12) when only `slices.Sort` AT INTEGER ELEMENTS was
// modeled — the quorum-pilot `sortSlice` machine op refused everything
// else by name — so that a silent widening of that surface would show as
// baseline drift; it flipped green when row M made every kind the generic,
// and it now pins that the re-admitted integer-only intercept leaves the
// non-integer kinds on the generic. Wider string/float/named-kind coverage:
// `slices/slices-sort-kinds/*`; the op's own shapes: `slices/slices-sort-op/*`.

import "slices"

func sortNonIntegerElements() int {
	xs := []string{"b", "a", "c"}
	slices.Sort(xs)
	if xs[0] == "a" {
		return 1
	}
	return 0
}
