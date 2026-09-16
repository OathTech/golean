package main

// R4 witness (target identity through slice replacement): the compound target's
// header is FROZEN when read; a call that rebinds a leaves the old storage
// observable through old. Relation set {old 11 20 / a 100 200, old 10 20 /
// a 101 200}; the hybrids (read one array, store into the other) are forbidden.
func main() {
	a := []int{10, 20}
	old := a
	mut := func() int { a = []int{100, 200}; return 1 }
	a[0] += mut()
	println("old", old[0], old[1])
	println("a", a[0], a[1])
}
