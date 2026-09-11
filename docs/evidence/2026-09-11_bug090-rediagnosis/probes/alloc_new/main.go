package main

// Allocation-only loop: one new(int) cell per iteration, no aggregate writes.
func probe(n int) int {
	s := 0
	for i := 0; i < n; i++ {
		p := new(int)
		*p = i
		s += *p
	}
	return s
}
func main() {}
