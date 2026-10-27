package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: a named result is declared in the
// function body's block, so a top-level `:=` of it declares nothing new (gc rejects).
func f() (r int) {
	r := 1
	return r
}

func main() { f() }
