package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell C10): the
// complement of sweep-s19-library-node — source-through libraries that
// are NOT nodes (cmp, math/bits) delay nothing: aaa goes first, 12.

import (
	_ "aaa"
	_ "bbb"
	"rec"
)

func libraryNonNodeGatesNothing() int { return rec.Seq }

func main() { println(libraryNonNodeGatesNothing()) }
