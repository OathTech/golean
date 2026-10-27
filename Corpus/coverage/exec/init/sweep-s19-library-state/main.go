package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell E1): a main-
// package initializer calls a SOURCE-THROUGH library function that reads
// the library's own package-level state (`strings.Fields` reads
// `asciiSpace`, a composite-literal initializer of the lowered `strings`
// unit): the library unit's initializers have run before main's.

import "strings"

var tr int

func mark(x int) int { tr = tr*10 + x; return x }

var e1n = len(strings.Fields(" a  b\tc ")) + mark(1)
var e1u = strings.ToUpper("ab")

func libraryStateBeforeMain() int { return tr*100 + e1n*10 + len(e1u) }

func main() { println(libraryStateBeforeMain()) }
