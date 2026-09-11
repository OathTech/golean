package main

// The 2026-09-11 review's workload (§13): byte appends growing from nil.
func probe(n int) int {
	var xs []byte
	for i := 0; i < n; i++ {
		xs = append(xs, byte(i))
	}
	return len(xs)
}
func main() {}
