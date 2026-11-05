package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group F3: an implementor BOXED while only Errorf (no dyn bundle) is injected — the boxing walk does not arm, static
// sites refuse only when the implementor is an operand; this program has none.
import "fmt"

type both int

func (both) Format(s fmt.State, verb rune) { fmt.Fprint(s, "via-format") }
func (both) String() string                { return "via-string" }

func errorfNoDynBoxed() string {
	var a any = both(1)
	_ = a
	return fmt.Errorf("x%d", 1).Error()
}

func main() {
	errorfNoDynBoxed()
}
