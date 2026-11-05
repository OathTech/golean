package main

// S23 sweep — resource budgets (docs/defect-shapes.md; the plan
// docs/2026-10-27_defect-neighbourhood-campaign.md §4; lane sweep/s23-budgets,
// 2026-11-05): an over-budget array type reached through a GENERIC
// instantiation. The frontend's per-declaration quarantine has no declared
// marker for an instantiated type, so this is the designed residual of the
// 2026-10-13 fix round (BUG-078, review LOW-2): the export refuses by name as
// a whole, which is why the subject has a package of its own. gc builds the
// program and answers 70002. RED BY DESIGN on BUG-078's Cases line.

type Box[T any] struct{ v T }

func genericOver() int {
	var b Box[[70000]int]
	b.v[1] = 2
	return len(b.v) + b.v[1]
}

func main() { println(genericOver()) }
