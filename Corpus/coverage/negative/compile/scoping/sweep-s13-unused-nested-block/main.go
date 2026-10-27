package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: an unused variable of an inner block.
func main() {
	x := 1
	{
		x := 2
	}
	println(x)
}
