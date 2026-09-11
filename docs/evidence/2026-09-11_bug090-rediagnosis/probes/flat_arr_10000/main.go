package main

// w element writes into a flat [10000]byte array variable.
func probe(w int) int {
	var b [10000]byte
	for i := 0; i < w; i++ {
		b[0] = byte(i)
	}
	return len(b) + int(b[0])
}
func main() {}
