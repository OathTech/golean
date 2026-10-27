package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: gc go1.26.5 rejects this directory with the
// substring in case.tsv and the native frontend refuses it as a rejection (or,
// for a row born FAIL at frontend-accepts, LOWERS it — the finding named below).
// B6: the module's go line is the language version; range over an int needs go1.22.
// The frontend refuses the module (the Go 1.26 language only, BUG-109).

func main() {
	n := 0
	for i := range 3 {
		n += i
	}
	println(n)
}
