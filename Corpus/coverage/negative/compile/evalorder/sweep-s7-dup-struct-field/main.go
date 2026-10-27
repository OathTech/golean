package main

// Defect-neighbourhood campaign, shape S7 (lane sweep/s7-hoist-order, 2026-10-27): a keyed
// struct literal naming the same field twice is rejected by gc (spec#Composite_literals:
// a field may be specified at most once).

type T struct{ a, b int }

func f() int { return 1 }

func main() {
	t := T{a: f(), a: f()}
	_ = t
}
