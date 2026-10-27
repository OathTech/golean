package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// D13: blank imports of stdlib packages (strings, fmt, os) are accepted on both
// sides and change nothing in the program.

import (
	_ "fmt"
	_ "os"
	_ "strings"
)

func blankImports() int { return 7 }
