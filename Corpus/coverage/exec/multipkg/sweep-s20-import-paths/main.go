package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// D17/D18: an import path element beginning with _ and a testdata element are
// ordinary to an explicit import (gc skips such directories only when matching
// patterns like ./...); both sides resolve them.

import (
	ulib "_lib"
	ux "lib/_x"
	tlib "testdata/lib"
)

func underscoreDir() int    { return ulib.F() }
func underscoreNested() int { return ux.F() }
func testdataDir() int      { return tlib.F() }
