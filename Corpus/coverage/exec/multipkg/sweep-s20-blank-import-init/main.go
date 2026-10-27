package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// D14: a blank import (_ "effect") still initializes the package — its init writes
// shared.X, which main reads (1); the named control effect2 does the same (11).

import (
	_ "effect"
	"effect2"
	"shared"
)

func blankImportInit() int { return shared.X }
func namedImportInit() int { return shared.Y + effect2.F() }
