package main

// Scalar-only loop: the machine's per-step baseline (one int cell write per iteration).
func probe(n int) int {
	s := 0
	for i := 0; i < n; i++ {
		s += i
	}
	return s
}
func main() {}
