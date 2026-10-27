package main

// Defect-neighbourhood campaign, shape S7 (lane sweep/s7-hoist-order, 2026-10-27): an array
// literal with two elements at the same constant index is rejected by gc
// (spec#Composite_literals: an index may appear only once).

func f() int { return 1 }

func main() {
	a := [3]int{1: f(), 1: f()}
	_ = a
}
