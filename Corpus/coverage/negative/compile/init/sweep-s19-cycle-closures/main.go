package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell A24): an
// initialization cycle through two CLOSURES stored in variables (f's
// body refers to g, g's to f).

var a24f = func() int { return a24g() }
var a24g = func() int { return a24f() }

func main() { println(a24f()) }
