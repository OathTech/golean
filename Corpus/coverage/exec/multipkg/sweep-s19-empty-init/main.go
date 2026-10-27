package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell C18): a package
// whose only declaration is `func init() {}` is pruned under both rules:
// la is ready at step one and beats lb — 12.

import (
	_ "la"
	_ "lb"
	"rec"
)

func emptyInitPruned() int { return rec.Seq }

func main() { println(emptyInitPruned()) }
