package main

// w scalar-field writes into a struct whose sibling field is a [1000]byte array.
type S struct {
	a [1000]byte
	x int
}

func probe(w int) int {
	var s S
	for i := 0; i < w; i++ {
		s.x = i
	}
	return s.x + len(s.a)
}
func main() {}
