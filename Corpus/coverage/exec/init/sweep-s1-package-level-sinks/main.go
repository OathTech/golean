package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// PACKAGE-LEVEL variable initializers (the package initializer's fabricated
// assignments, BUG-079's other route): an untyped constant of each kind, nil,
// a typed-nil pointer, a defined value and a narrower concrete value into
// interface-typed globals; an interface-keyed map literal; a call result.

type tDef int

type tErr struct{}

func (*tErr) Error() string { return "tErr" }

type tR interface{ R() int }

type tBoth struct{ n int }

func (b tBoth) R() int { return b.n }

func mkInt() int { return 7 }

var gInt any = 1

var gFloat any = 2.5

var gRune any = 'a'

var gStr any = "s"

var gBool any = true

var gNil error = nil

var gTypedNil error = (*tErr)(nil)

var gDef any = tDef(3)

var gNarrow tR = tBoth{4}

var gMap = map[any]int{1: 10, 2.5: 20}

var gCall any = mkInt()

var gShift any = 1 << gS

var gS = 3

func constants() (any, any, any, any, any) { return gInt, gFloat, gRune, gStr, gBool }

func nils() (bool, bool, string) { return gNil == nil, gTypedNil == nil, gTypedNil.Error() }

func definedAndNarrower() (any, int) { return gDef, gNarrow.R() }

func mapKeys() (int, int, int) { return gMap[1], gMap[1.0], gMap[2.5] }

func callAndShift() (any, any) { return gCall, gShift }

func main() {
	constants()
}
