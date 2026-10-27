package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// A7.1: the file starts with a UTF-8 BOM (gc skips it; the
// literal below spells its invalid byte with an escape).

func bomAtStart() (int, string) {
	s := "bom\xff"
	return len(s), s
}

func main() {
	bomAtStart()
}
