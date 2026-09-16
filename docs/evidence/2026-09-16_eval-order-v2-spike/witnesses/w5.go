package main

// F5 witness: per-activation binder lifetime. Iteration 2 must panic
// in every execution; no execution prints 7 twice.
func main() {
	defer func() { println("w5 panic:", recover().(error).Error()) }()
	a := []int{7}
	mut := func() int { a = nil; return 0 }
	for j := 0; j < 2; j++ {
		println("w5 iter", j, a[0]+mut())
	}
}
