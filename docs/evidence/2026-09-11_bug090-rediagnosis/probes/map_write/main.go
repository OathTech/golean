package main

// Map-write loop: n distinct int keys.
func probe(n int) int {
	m := map[int]int{}
	for i := 0; i < n; i++ {
		m[i] = i
	}
	return len(m)
}
func main() {}
