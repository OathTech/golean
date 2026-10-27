package main

import (
	"errors"
	"fmt"
)

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The fmt shim's MODELED verbs (%s %v %d %t) over invalid / NUL / multi-byte
// arguments, Sprint / Errorf / Sprintln carrying such bytes, and errors.New.
// Outside the shim's subset and recorded as gaps, not rowed: %q on any byte
// >= 0x80 (the ASCII quoter's recorded bound, a run-time refusal), %x over a
// string or an int argument, %X, %w, %c, %U and the + / # flags on %q.

func sprintfModeledVerbs() (string, string) {
	s := "a\xff\x00é"
	return fmt.Sprintf("%s|%v", s, s), fmt.Sprintf("%d|%t", len(s), true)
}

func sprintAndErrorf() (string, int, string, string) {
	a := fmt.Sprint("\xff", "\x00", "é", 1)
	e := fmt.Errorf("bad %s: %v", "\xff\x00", errors.New("inner\x01"))
	return a, len(a), e.Error(), fmt.Sprintln("x\xffy")
}

func errorsNewBytes() (string, int, bool) {
	e := errors.New("a\x00\xff\u0085é😀")
	s := e.Error()
	return s, len(s), s == "a\x00\xff\u0085é😀"
}

func main() {
	sprintfModeledVerbs()
}
