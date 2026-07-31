package main

// The `slices.Sort` extern's REFUSAL boundary, pinned as a red
// `frontend-export` row so a silent widening of the modeled surface shows
// up as baseline drift (pre-merge audit 2026-07-31, finding 12). Only
// `slices.Sort` AT INTEGER ELEMENTS is modeled; a string element type is
// refused at the frontend, and the refusal must stay refused until a real
// string-ordering model lands.

import "slices"

func sortNonIntegerElements() int {
	xs := []string{"b", "a", "c"}
	slices.Sort(xs)
	if xs[0] == "a" {
		return 1
	}
	return 0
}
