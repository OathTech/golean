package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: a method declaration inside a function body.
type L struct{}

func main() {
	func (l L) M() int { return 1 }
}
