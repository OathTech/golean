package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: `_, b :=` with b in the SAME block
// declares nothing new (the blank does not count).
func two() (int, int) { return 1, 2 }

func main() {
	b := 1
	_, b := two()
	println(b)
}
