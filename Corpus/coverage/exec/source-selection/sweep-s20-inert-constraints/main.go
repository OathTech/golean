package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// A11/A12/A23: a constraint over custom tags only that is TRUE with no -tags
// is inert — //go:build !sweepfoo, the legacy // +build !sweepfoo, a tautology —
// and the file's init runs on both sides. (A19, a //go:build ignore line after
// a UTF-8 BOM, was a fourth subject here until the BUG-216 fix, lane
// frontend/fix-admission-1027, 2026-10-27: go/build strips the BOM and honours
// the line, so the file is excluded on both sides (gc: 0) and the standing
// constraint policy refuses it by name — the mirrored header rule now reaches
// it; the shape is pinned by the lane's probe a19 and the fileselect unit test.)

var a, b, c int

func gobuildInert() int    { return a }
func plusbuildInert() int  { return b }
func customTautology() int { return c }
