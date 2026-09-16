package main

// F3 witness: once-evaluated lvalue identity shared by read and store.
// Relation set {[11 20], [10 21]}; the hybrid [10 11] is forbidden.
func main() {
	a := []int{10, 20}
	i := 0
	mut := func() int { i = 1; return 1 }
	a[i] += mut()
	println("w3", a[0], a[1])
}
