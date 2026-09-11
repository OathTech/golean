package main

// The BUG-090 audit probe: make([]byte, 4) per iteration.
func probe(n int) int {
	s := 0
	for i := 0; i < n; i++ {
		b := make([]byte, 4)
		s += len(b)
	}
	return s
}
func main() {}
