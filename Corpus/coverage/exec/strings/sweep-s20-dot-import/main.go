package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// D12: a dot-import of an admitted stdlib package (strings): the bare identifiers
// resolve to the package's members on both sides.

import . "strings"

func dotImportStrings() int { return len(ToUpper("ab")) + Index("abc", "c") }
