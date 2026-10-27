package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// BUG-217 (born RED, frontend-accepts): the main module is named fmt, so the main
// package's import path is a standard-library package; gc refuses (ambiguous import)
// and the frontend exports the program.

func main() { println(7) }
