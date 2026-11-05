package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group B5: Sprint's space rule (goleanShimFmtSprintDyn): a space iff NEITHER neighbour is a string — gc judges by
// reflect.Kind (a NAMED string kind counts), the shim by the concrete type `string`. The named-string-kind rows are
// born RED (BUG-400).
import (
	"errors"
	"fmt"
)

type I int

func (I) String() string { return "I" }

type S string

func (s S) String() string { return string(s) }

type E string

func (e E) Error() string { return string(e) }

func pairs() string {
	return "[" + fmt.Sprint("a", "b") + "][" + fmt.Sprint("a", 1) + "][" + fmt.Sprint(1, "a") + "][" + fmt.Sprint(1, 2) + "][" +
		fmt.Sprint(1, true) + "][" + fmt.Sprint(true, false) + "][" + fmt.Sprint(nil, 1) + "][" + fmt.Sprint(1, nil) + "][" +
		fmt.Sprint(errors.New("e"), 1) + "][" + fmt.Sprint([]byte("b"), 1) + "][" + fmt.Sprint("a", nil) + "][" + fmt.Sprint(uint8(1), int8(2)) + "]"
}
func intStringerPair() string { return fmt.Sprint(I(1), I(2)) + "|" + fmt.Sprint(I(1), "x", I(2)) }
func empties() (string, string, string, string) {
	return fmt.Sprint(), fmt.Sprintln(), fmt.Sprint(nil, nil), fmt.Sprintln(nil)
}
func fixedMixed() string {
	return fmt.Sprint("a", 1, "b", true, uint8(2)) + "|" + fmt.Sprint(1, 2, 3, "x", "y", 4)
}
func sprintlnMixed() string {
	return fmt.Sprintln("a", 1, "b") + fmt.Sprintln(1, 2) + fmt.Sprintln("x")
}
func namedStringStringer() string      { return fmt.Sprint(S("a"), S("b")) }
func namedStringStringerMixed() string { return fmt.Sprint(S("a"), 1, S("b"), "c", 2) }
func namedStringError() string         { return fmt.Sprint(E("x"), E("y")) }
func namedStringErrorThenInt() string  { return fmt.Sprint(E("x"), 1) }
func spreadNamedString() string {
	g := func(v ...any) string { return fmt.Sprint(v...) }
	return g(S("a"), S("b"), 1)
}
func namedStringSprintln() string { return fmt.Sprintln(S("a"), S("b")) }

func main() {
	pairs()
	intStringerPair()
	empties()
	fixedMixed()
	sprintlnMixed()
	namedStringStringer()
	namedStringStringerMixed()
	namedStringError()
	namedStringErrorThenInt()
	spreadNamedString()
	namedStringSprintln()
}
