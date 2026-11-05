package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group E1 (BUG-086's shape): the desugar entry `spread-sprintf` planted ALONE — its bundle must be closed under its own references.
import "fmt"

func alone() string {
	g := func(f string, v ...any) string { return fmt.Sprintf(f, v...) }
	return g("%d|%s", 1, "a")
}

func main() {
	alone()
}
