package main

import "sync"

// gc updates the counter BEFORE panicking (probe p13): after a
// recovered negative-counter panic the counter is negative, and Wait
// unblocks only at exactly 0 — the waiter parks forever and the
// program deadlocks. A model that panicked before applying the delta
// (counter left 0) would let Wait return and print 1.
func negativeAfterRecover() int {
	var wg sync.WaitGroup
	wg.Add(1)
	wg.Done()
	func() {
		defer func() {
			_ = recover()
		}()
		wg.Done()
	}()
	ch := make(chan int)
	go func() {
		wg.Wait()
		ch <- 1
	}()
	return <-ch
}

func main() {
	negativeAfterRecover()
}
