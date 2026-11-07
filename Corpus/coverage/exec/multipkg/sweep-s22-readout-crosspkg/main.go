package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md; the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Group A7/A8 across packages: reflect.Type.Name() is unqualified for a named type, and an instantiation's
// argument carries its package path inside the bracket.

import "note"

type Tag[T any] struct{ N int }
type Holder struct {
	note.T
	Extra note.Kind
}

func directAndBoxed() (note.T, any) { return note.T{V: 1}, note.T{V: 2} }
func embeddedForeign() Holder       { return Holder{note.T{V: 3}, note.Kind(4)} }
func instantiatedAtForeign() (Tag[note.T], any, note.Pair[int]) {
	return Tag[note.T]{N: 1}, Tag[note.T]{N: 2}, note.Pair[int]{A: 1, B: "b"}
}
func foreignDefinedKinds() (note.Kind, note.Name, any, any) {
	return note.Kind(5), note.Name("n"), note.Kind(6), note.Name("m")
}

func main() {
	directAndBoxed()
	embeddedForeign()
	instantiatedAtForeign()
	foreignDefinedKinds()
}
