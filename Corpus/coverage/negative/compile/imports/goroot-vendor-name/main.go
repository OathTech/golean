package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// BUG-219 (born RED, frontend-accepts): the path vendor names GOROOT/src/vendor to
// gc (no Go files there); the frontend resolves the case-local directory.

import x "vendor"

func main() { println(x.F()) }
