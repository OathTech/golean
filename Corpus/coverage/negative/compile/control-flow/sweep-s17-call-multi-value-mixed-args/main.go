package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17: a form gc rejects;
// the frontend must refuse it as a rejection (plan §4). Expected: gc rejects.

func two() (int, int) { return 1, 2 }
func g(a, b, c int) int { return a + b + c }
func f() int { return g(two(), 1) }
func main() { f() }
