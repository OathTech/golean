package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// BUG-401 (found by this sweep): a fmt desugar whose helper references the force-quarantined refusal helper, reached
// from package initialization — H-11's init reach walk refuses the WHOLE export naming a run-time bound no run hits.
// Born RED; the sibling forms (%d / %x / Errorf in an initializer) are green in fmt/sweep-s21-contexts.
import "fmt"

type st int

func (st) String() string { return "st" }

var g = fmt.Sprintf("%q", "x")

func r() string { return g }

func main() {
	r()
}
