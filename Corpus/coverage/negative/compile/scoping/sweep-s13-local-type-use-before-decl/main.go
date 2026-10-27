package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: a function-local type's scope begins at
// its declaration; an earlier use is undefined.
func main() {
	x := T(1)
	type T int
	println(x)
}
