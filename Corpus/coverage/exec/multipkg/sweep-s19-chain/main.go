package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell C3): a TRANSITIVE
// import chain main → ch1 → ch2 → ch3: the deepest initializes first
// (schedule 3 2 1) and each level sees the next's value.

import (
	"ch1"
	"rec"
)

// chainSeq is 321.
func chainSeq() int { return rec.Seq }

// chainValue is 6: 1 + (2 + 3).
func chainValue() int { return ch1.V }

func main() { println(chainSeq(), chainValue()) }
