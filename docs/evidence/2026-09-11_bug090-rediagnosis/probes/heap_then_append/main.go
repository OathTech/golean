package main

// h live cells allocated first, then w in-place appends into a cap-w slice.
func probe(h int, w int) int {
	for j := 0; j < h; j++ {
		p := new(int)
		*p = j
	}
	xs := make([]byte, 0, w)
	for i := 0; i < w; i++ {
		xs = append(xs, byte(i))
	}
	return len(xs)
}
func main() {}
