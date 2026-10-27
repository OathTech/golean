package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// C11/C12: //export without cgo is prose; a comment whose text begins with a blank
// (// go:noinline) is not a directive; words after //go:noinline are ignored.

//export exportProse
func exportProse() int { return 7 }

// go:noinline
func spaceNoinline() int { return 7 }

//go:noinline because reasons
func noinlineExtraWords() int { return 7 }
