package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17: a form gc rejects;
// the frontend must refuse it as a rejection (plan §4). Expected: gc rejects.

type pt struct{ x int }
func f() { m := map[string]pt{}; m["a"].x++ }
func main() { f() }
