package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17: a form gc rejects;
// the frontend must refuse it as a rejection (plan §4). Expected: gc rejects.

func f(x int) {
	switch x {
	case 1:
		continue
	}
}
func main() { f(1) }
