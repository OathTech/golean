package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// C3: //go:embed on a var inside a function body.

import _ "embed"

func main() {
	//go:embed data.txt
	var s string
	println(len(s))
}
