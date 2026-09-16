package main

// Fragment extra: a buffered receive as the sibling event of a failing
// compound-target read (BUG-104's recv row shape). Witness: len(ch) after.
func main() {
	ch := make(chan int, 1)
	ch <- 5
	x := []int{1}
	f := func() int { return 9 }
	func() {
		defer func() { println("x3 panic:", recover().(error).Error()) }()
		x[f()] += <-ch
	}()
	println("x3 len(ch)", len(ch))
}
