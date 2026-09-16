package main

// F2 witness: sub-occurrence interleaving. Relation set {10, 30, 40}.
func main() {
	a := []int{10, 20}
	b := []int{0}
	mut := func() int { a[0] = 30; a[1] = 40; b[0] = 1; return 0 }
	v := a[b[0]] + mut()
	println("w2", v)
}
