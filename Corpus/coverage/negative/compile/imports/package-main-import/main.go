package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// BUG-219 (born RED, frontend-accepts): importing a package main (aliased, so no
// name collision in the importer) — cmd/go refuses, the frontend exports.

import p "prog"

func main() { println(p.F()) }
