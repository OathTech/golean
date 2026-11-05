package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17: a form gc rejects;
// the frontend must refuse it as a rejection (plan §4). Expected: gc rejects.

func f(s []int) int {
	switch s {
	case s:
		return 1
	}
	return 0
}
func main() { f(nil) }
