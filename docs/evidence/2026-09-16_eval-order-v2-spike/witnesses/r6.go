package main

// R6 witness (header granularity): a base/header producer separate from the one
// checked access gives {10, 20}; a fused header+check+load read narrows to {20}.
func main() {
	a := []int{10}
	f := func() int { a = []int{20}; return 0 }
	println("header", a[f()])
}
