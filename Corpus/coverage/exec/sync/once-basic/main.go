package main

import "sync"

// f runs exactly once across repeated Do calls on the same Once.
func onceRunsOnce() int {
	var o sync.Once
	n := 0
	o.Do(func() { n = n + 1 })
	o.Do(func() { n = n + 1 })
	o.Do(func() { n = n + 1 })
	return n
}

// A panicking f counts as COMPLETED (probe p05; sync/once.go sets done
// in a defer): the panic propagates out of Do (recoverable), and a
// later Do does not run its f.
func oncePanickingF() int {
	var o sync.Once
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 10
			}
		}()
		o.Do(func() { panic("boom") })
	}()
	called := 0
	o.Do(func() { called = 1 })
	return r*100 + called
}

// The Once edge across goroutines (sync/once.go: "the return from f
// 'synchronizes before' the return from any call of once.Do(f)"):
// whichever side runs f, both observe its write — exactly one f runs,
// and the readout is 42 on every schedule.
func onceAcrossGoroutines() int {
	var o sync.Once
	x := 0
	done := make(chan int)
	go func() {
		o.Do(func() { x = x + 42 })
		done <- 1
	}()
	o.Do(func() { x = x + 42 })
	<-done
	return x
}

func main() {
	onceRunsOnce()
	oncePanickingF()
	onceAcrossGoroutines()
}
