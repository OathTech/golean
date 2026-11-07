package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22: a print operand gc rejects; the frontend must refuse it as a
// rejection (plan §4). Expected: gc rejects.

func f()    { println([2]int{1, 2}) }
func main() { f() }
