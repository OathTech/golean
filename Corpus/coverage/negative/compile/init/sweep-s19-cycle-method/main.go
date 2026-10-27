package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell A23): an
// initialization cycle through a METHOD body (a refers to t.m, m refers
// to a).

type a23t struct{}

func (a23t) m() int { return a23a }

var a23a = a23t{}.m()

func main() { println(a23a) }
