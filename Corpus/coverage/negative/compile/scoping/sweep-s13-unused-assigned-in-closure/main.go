package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: a variable only assigned inside a
// closure is still unused.
func main() {
	x := 1
	func() { x = 2 }()
}
