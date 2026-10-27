package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// BUG-221 (born RED, frontend-accepts): a 1 GB array parameter makes the frame
// exceed gc's limit (ssagen/pgen.go); the frontend sizes the type (within the
// address-space limit) and exports.

//go:noinline
func f(a [1 << 27]int64) int { return int(a[3]) }

var big [1 << 27]int64

func main() { big[3] = 1; println(f(big)) }
