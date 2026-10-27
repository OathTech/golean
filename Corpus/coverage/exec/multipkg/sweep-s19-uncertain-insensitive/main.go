package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell C17): an
// UNCERTAIN (maybe-static) package in an INSENSITIVE position — both la
// and lb import zq, so every pruning orders them the same way and the
// BUG-061 guard lets the program lower (its enumeration finds no
// sensitive assignment). 12 either way, and zq's array is in place.

import (
	_ "la"
	_ "lb"
	"rec"
	"zq"
)

func uncertainInsensitive() int { return rec.Seq*10 + zq.A[2] }

func main() { println(uncertainInsensitive()) }
