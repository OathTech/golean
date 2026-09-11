package main

// w element writes at a fixed index into a slice of length m.
func probe(m int, w int) int {
	xs := make([]byte, m)
	for i := 0; i < w; i++ {
		xs[0] = byte(i)
	}
	return len(xs) + int(xs[0])
}
func main() {}
