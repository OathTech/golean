package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: an assignment is not a use.
func main() {
	x := 0
	x = 1
}
