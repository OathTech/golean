package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: a type-switch guard variable unused in
// every clause.
func main() {
	var x any = 1
	switch v := x.(type) {
	case int:
		println("int")
	}
}
