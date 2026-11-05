package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group E2 (BUG-086's shape across units): the local package uses Errorf only, main uses Sprint / Sprintf only — each unit
// gets its own bundle; main renders a Stringer DECLARED in the local package.
import (
	"fmt"

	"note"
)

func crossErrorfThenSprint() string { return fmt.Sprint(note.Make(3).Error(), 1) }
func crossStringer() string         { return fmt.Sprintf("%v|%s", note.Tag(2), note.Tag(3)) }

func main() {
	crossErrorfThenSprint()
	crossStringer()
}
