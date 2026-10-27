package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: an unused if-init variable.
func main() {
	if x := 1; true {
		println("yes")
	}
}
