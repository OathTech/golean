package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the type-switch guard's per-clause
// binding lives in the clause's own block, so a `:=` of the same name directly in the clause
// declares nothing new.
func main() {
	var x any = 5
	switch v := x.(type) {
	case int:
		v := v * 2
		println(v)
	}
}
