package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: an unused select-case variable.
func main() {
	ch := make(chan int, 1)
	ch <- 1
	select {
	case v := <-ch:
		println("got")
	}
}
