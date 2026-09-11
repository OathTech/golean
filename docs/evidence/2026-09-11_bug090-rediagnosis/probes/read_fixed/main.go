package main

// w element reads at a fixed index from a slice of length m (no aggregate write).
func probe(m int, w int) int {
	xs := make([]byte, m)
	s := 0
	for i := 0; i < w; i++ {
		s += int(xs[0])
	}
	return s + len(xs)
}
func main() {}
