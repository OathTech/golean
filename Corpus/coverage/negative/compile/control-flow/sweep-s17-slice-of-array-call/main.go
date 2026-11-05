package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17: a form gc rejects;
// the frontend must refuse it as a rejection (plan §4). Expected: gc rejects.

func arr() [3]int { return [3]int{1, 2, 3} }
func f() []int { return arr()[:] }
func main() { f() }
