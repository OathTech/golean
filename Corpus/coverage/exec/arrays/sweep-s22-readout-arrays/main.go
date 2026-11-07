package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md; the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Group A6: arrays observe as `values` lists; a defined array type carries no name of its own.

type P struct {
	X int
	S string
}
type Box[T any] struct{ V T }
type A3 [3]int

func zeroLength() ([0]int, [0]P, int) { return [0]int{}, [0]P{}, len([0]int{}) }
func bools() [3]bool                  { return [3]bool{true, false, true} }
func nested() ([2][2]int, [1][1][1]string) {
	return [2][2]int{{1, 2}, {3, 4}}, [1][1][1]string{{{"deep"}}}
}
func stringsAndStructs() ([2]string, [2]P) { return [2]string{"a", "bc"}, [2]P{{1, "x"}, {2, "y"}} }
func mixedBoxes() [4]any                   { return [4]any{1, "s", nil, P{3, "z"}} }
func instantiations() ([2]Box[int], [1]Box[string]) {
	return [2]Box[int]{{1}, {2}}, [1]Box[string]{{"v"}}
}
func definedArrayType() (A3, [2]A3) { return A3{1, 2, 3}, [2]A3{{4, 5, 6}, {7, 8, 9}} }

func main() {
	zeroLength()
	bools()
	nested()
	stringsAndStructs()
	mixedBoxes()
	instantiations()
	definedArrayType()
}
