package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group E3: the injection scan keys the import's LOCAL name — an aliased import f of fmt.
import f "fmt"

type st int

func (st) String() string { return "st" }

func aliasSprintf() string { return f.Sprintf("%d|%v", 1, st(1)) }
func aliasErrorf() string  { return f.Errorf("e%d", 2).Error() }
func aliasSprintSpread() string {
	g := func(v ...any) string { return f.Sprint(v...) }
	return g(1, "a", st(1)) + "|" + f.Sprintln("x", 1)
}

func main() {
	aliasSprintf()
	aliasErrorf()
	aliasSprintSpread()
}
