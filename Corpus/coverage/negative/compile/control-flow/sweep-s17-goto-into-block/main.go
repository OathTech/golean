package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17: a form gc rejects;
// the frontend must refuse it as a rejection (plan §4). Expected: gc rejects.

func f(x int) int {
	if x > 0 {
		goto L
	}
	{
	L:
		x++
	}
	return x
}
func main() { f(1) }
