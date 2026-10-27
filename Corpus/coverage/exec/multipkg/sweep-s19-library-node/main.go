package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell C9): BUG-060's
// shape with a SOURCE-THROUGH library as the gating stdlib node. aaa
// sorts before bbb but imports strings (a node); bbb imports only the
// pruned recorder: 21, not 12.

import (
	_ "aaa"
	_ "bbb"
	"rec"
)

func libraryNodeGates() int { return rec.Seq }

func main() { println(libraryNodeGates()) }
