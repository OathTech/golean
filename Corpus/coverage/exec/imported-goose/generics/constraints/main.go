// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/generics/constraints.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func UnderlyingSlice[T ~[]int](s T) int {
	return len(s)
}

// Clone copies a generic slice.
//
// Slightly simplified from [slices.Clone].
func Clone[S ~[]E, E any](s S) S {
	return append(S{}, s...)
}

// --- GoLean harness ---
// Authored wrapper: underlying-slice constraint + generic Clone.

func goleanConstraints() int {
	s := []int{1, 2, 3}
	return UnderlyingSlice(s)*100 + len(Clone(s))*10 + Clone(s)[2]
}

func main() {}
