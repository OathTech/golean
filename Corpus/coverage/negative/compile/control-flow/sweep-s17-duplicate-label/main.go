package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17: a form gc rejects;
// the frontend must refuse it as a rejection (plan §4). Expected: gc rejects.

func f() int {
	n := 0
L:
	for i := 0; i < 2; i++ {
		n++
		break L
	}
L:
	for i := 0; i < 2; i++ {
		n++
		break L
	}
	return n
}
func main() { f() }
