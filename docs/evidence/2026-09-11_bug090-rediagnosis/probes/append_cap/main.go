package main

// w in-place appends into a slice preallocated with capacity c (w <= c: no spill).
// Fixed w with varying c isolates "cost grows with the backing array" from
// "cost grows with the iteration count".
func probe(c int, w int) int {
	xs := make([]byte, 0, c)
	for i := 0; i < w; i++ {
		xs = append(xs, byte(i))
	}
	return len(xs)
}
func main() {}
