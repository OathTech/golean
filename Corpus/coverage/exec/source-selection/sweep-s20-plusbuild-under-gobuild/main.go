package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// BUG-216 (born RED, FAIL/frontend-export): a // +build line under a //go:build line (gc honours the //go:build line only).
// gc INCLUDES extra.go (its init runs: 2); the frontend refuses the export saying the
// oracle would compile without the file.

var x = 1

func includedInit() int { return x }
