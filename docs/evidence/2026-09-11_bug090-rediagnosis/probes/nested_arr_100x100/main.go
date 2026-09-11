package main

// w element writes into a [100][100]byte array variable (same 10,000 elements, nested).
func probe(w int) int {
	var a [100][100]byte
	for i := 0; i < w; i++ {
		a[0][0] = byte(i)
	}
	return len(a) + int(a[0][0])
}
func main() {}
