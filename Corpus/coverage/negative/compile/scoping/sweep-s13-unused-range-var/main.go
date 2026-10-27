package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: an unused range variable.
func main() {
	for i := range []int{1, 2} {
	}
}
