package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: a blank type-switch guard.
func main() {
	var x any = 1
	switch _ := x.(type) {
	case int:
		println("int")
	}
}
