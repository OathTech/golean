package main

// Defect-neighbourhood campaign, shape S7 (lane sweep/s7-hoist-order, 2026-10-27): a map
// literal with two constant keys that are equal is rejected by gc (spec#Composite_literals:
// duplicate constant keys are a compile-time error), so no order question arises.

func f() int { return 1 }

func main() {
	m := map[int]int{1: f(), 1: f()}
	_ = m
}
