package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell A22): an
// initialization cycle THROUGH A FUNCTION BODY (a refers to f, f refers
// to a) — spec#Package_initialization: "the program is not valid".

var a22a = a22f()

func a22f() int { return a22a }

func main() { println(a22a) }
