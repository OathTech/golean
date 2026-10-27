package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// BUG-221 (born RED, frontend-accepts): a struct parameter of 17 arrays of 64 MB
// (1088 MB of args) exceeds gc's 1 GB frame limit; the frontend exports.

type S struct {
	A0 [1 << 23]int64
	A1 [1 << 23]int64
	A2 [1 << 23]int64
	A3 [1 << 23]int64
	A4 [1 << 23]int64
	A5 [1 << 23]int64
	A6 [1 << 23]int64
	A7 [1 << 23]int64
	A8 [1 << 23]int64
	A9 [1 << 23]int64
	A10 [1 << 23]int64
	A11 [1 << 23]int64
	A12 [1 << 23]int64
	A13 [1 << 23]int64
	A14 [1 << 23]int64
	A15 [1 << 23]int64
	A16 [1 << 23]int64
}

//go:noinline
func f(s S) int { return int(s.A0[3]) }

var big S

func main() { big.A0[3] = 1; println(f(big)) }
