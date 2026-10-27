package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// BUG-219 (born RED, frontend-accepts): an import path with a vendor element —
// cmd/go refuses (vendored packages are imported by their suffix), the frontend
// resolves vendor/lib as a case-local directory and exports.

import x "vendor/lib"

func main() { println(x.F()) }
