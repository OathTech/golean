	//go:build !sweepfoo

package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// C14: an indented //go:build line is a constraint to go/build and a directive on
// its own line to gc; inert here (custom tag), included on both sides.

func buildIndented() int { return 7 }
