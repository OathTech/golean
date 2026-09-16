package main

// R1 witness (second review): two reads and one mutating call, no order among the
// reads. Relation set {0, 1, 2, 3}; the retired read-order reduction loses 1
// (the order read y; mut(); read x). The reads cannot fail.
func main() {
	x, y := 0, 0
	mut := func() int { x = 1; y = 2; return 0 }
	println("reduction", x+y+mut())
}
