package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell C16's
// `errors.New` member): a package with a maybe-static initializer is
// still a CERTAIN node when it imports a node — la waits for zq, lb
// records first: 21.

import (
	_ "la"
	_ "lb"
	"rec"
)

func importMakesNode() int { return rec.Seq }

func main() { println(importMakesNode()) }
