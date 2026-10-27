package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// A11/A12/A23/A19: a constraint over custom tags only that is TRUE with no -tags
// is inert — //go:build !sweepfoo, the legacy // +build !sweepfoo, a tautology —
// and the file's init runs on both sides; a //go:build ignore line after a UTF-8
// BOM is a constraint to go/build (it strips the BOM) and the file is excluded on
// both sides (gc: 0).

var a, b, c, d int

func gobuildInert() int    { return a }
func plusbuildInert() int  { return b }
func customTautology() int { return c }
func bomIgnoreExcluded() int { return d }
