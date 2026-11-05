package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17: a form gc rejects;
// the frontend must refuse it as a rejection (plan §4). Expected: gc rejects.

func f(v any) int {
	switch v.(type) {
	case int:
		fallthrough
	case string:
		return 1
	}
	return 0
}
func main() { f(1) }
