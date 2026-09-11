package main

// w element writes into the first of 10 inner slices of length m/10 each
// (m elements total, each inner backing array its own heap cell).
func probe(m int, w int) int {
	xs := make([][]byte, 10)
	for j := 0; j < 10; j++ {
		xs[j] = make([]byte, m/10)
	}
	for i := 0; i < w; i++ {
		xs[0][0] = byte(i)
	}
	return len(xs) + int(xs[0][0])
}
func main() {}
