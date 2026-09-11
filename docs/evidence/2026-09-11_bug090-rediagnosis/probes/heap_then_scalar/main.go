package main

// h live cells allocated first, then a fixed scalar loop of w iterations.
// (h, 0) measures the allocation phase alone; (h, w) minus (h, 0) is the
// scalar phase's cost at heap size h.
func probe(h int, w int) int {
	for j := 0; j < h; j++ {
		p := new(int)
		*p = j
	}
	s := 0
	for i := 0; i < w; i++ {
		s += i
	}
	return s
}
func main() {}
