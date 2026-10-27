package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: a short variable declaration cannot be
// the post statement of a for clause.
func main() {
	for i := 0; i < 3; j := i + 1 {
		println(j)
	}
}
