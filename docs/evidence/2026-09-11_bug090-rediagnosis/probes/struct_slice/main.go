package main

// w scalar-field writes into a struct whose sibling is a SLICE of length m
// (the backing array is a separate heap cell).
type S struct {
	a []byte
	x int
}

func probe(m int, w int) int {
	var s S
	s.a = make([]byte, m)
	for i := 0; i < w; i++ {
		s.x = i
	}
	return s.x + len(s.a)
}
func main() {}
