package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// A1/A2/D28: a _test.go file (package main or package main_test) is never part of
// the program — its init never runs — while two ordinary inits run in source order.

var x = 0

func init() { x = x*10 + 1 }

func init() { x = x*10 + 2 }

func twoInitsNoTestInit() int { return x }
