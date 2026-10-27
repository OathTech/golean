package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// B9: the nested module sub/ declares go 1.21 and ranges over an int; its own go
// line governs it (gc rejects sub; the frontend refuses the nested go.mod by name).

import "sub"

func main() { println(sub.F()) }
