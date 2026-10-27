package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell C6): the
// tie-break is by LINKER SYMBOL NAME (multipkg/init-order-tiebreak pins
// the hyphen); '+' is the other import-path byte below '.' (0x2e) that
// the frontend admits, and it inverts the import-path order the same
// way: "x+y..inittask" < "x..inittask" while "x" < "x+y".

import (
	"rec"
	_ "x"
	_ "x+y"
)

// tiebreakPlus is 21 — x+y initializes first.
func tiebreakPlus() int { return rec.Seq }

func main() { println(tiebreakPlus()) }
