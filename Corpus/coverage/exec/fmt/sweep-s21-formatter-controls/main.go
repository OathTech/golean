package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group F3 (BUG-071 / BUG-153's controls): a Formatter implementor that is never boxed with the dyn bundle injected
// (exports; the dyn site renders its other operands), and one boxed where NO dyn bundle is injected (Errorf only).
import "fmt"

type both int

func (both) Format(s fmt.State, verb rune) { fmt.Fprint(s, "via-format") }
func (both) String() string                { return "via-string" }

func neverBoxed() string {
	b := both(1)
	_ = b
	return fmt.Sprint(1, "x") + fmt.Sprintf("%d", 2)
}

func main() {
	neverBoxed()
}
