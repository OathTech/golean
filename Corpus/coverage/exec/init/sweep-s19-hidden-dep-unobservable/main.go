package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell D6): an
// interface call in an initializer whose method reads NO initialized
// package variable — the E7 detector's OBSERVABLE condition must not
// fire, the program lowers, and both sides realize the declaration
// order (x then y).

var tr int

func mark(x int) int { tr = tr*10 + x; return x }

type d6I interface{ val() int }

type d6T struct{}

func (d6T) val() int { return 7 }

var d6x = d6I(d6T{}).val() + mark(2)
var d6y = mark(1)

func unobservableInterfaceCall() int { return tr*100 + d6x + d6y - 1 }

func main() { println(unobservableInterfaceCall()) }
