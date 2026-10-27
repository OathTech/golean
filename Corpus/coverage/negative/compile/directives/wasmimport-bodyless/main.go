package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// C6: //go:wasmimport on linux/amd64 leaves a body-less function, which gc rejects
// (the frontend refuses the directive itself, at file selection).

//go:wasmimport env f
func f() int32

func main() { println(f()) }
