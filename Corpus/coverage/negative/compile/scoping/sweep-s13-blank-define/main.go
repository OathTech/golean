package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the blank identifier declares no variable,
// so `_ :=` declares nothing new.
func main() {
	_ := 1
}
