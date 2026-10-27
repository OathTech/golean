package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// D24/D25: the file set of a case-local package is selected like the main
// package's — _x.go and x_windows.go are excluded (their inits never run: 1), an
// inert custom constraint's file is included (its init runs: 2).

import (
	"libexcl"
	"libinert"
)

func localExcludedFiles() int   { return libexcl.X }
func localInertConstraint() int { return libinert.X }
