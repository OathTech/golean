package main

import "sync"

var wgShared int

// The WaitGroup edge (sync/waitgroup.go: "a call to Done 'synchronizes
// before' the return of any Wait call that it unblocks" — probe p16's
// shape): the worker's write is visible after Wait on every schedule.
func addDoneWait() int {
	wgShared = 0
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		wgShared = 42
		wg.Done()
	}()
	wg.Wait()
	return wgShared
}

// Counter arithmetic without blocking: Add(2), two Dones, and a Wait
// that proceeds immediately at counter 0 (single goroutine — the
// fast-path Wait still performs its acquire, gc waitgroup.go:172).
func batchDone() int {
	var wg sync.WaitGroup
	wg.Add(2)
	wg.Done()
	wg.Done()
	wg.Wait()
	return 6
}

// The negative-counter panic is RECOVERABLE (probe p04 — a real
// panic(), unlike the mutex fatals) and execution continues normally
// after the recover.
func recoveredNegativeContinue() int {
	var wg sync.WaitGroup
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 5
			}
		}()
		wg.Done()
	}()
	return r
}

func main() {
	addDoneWait()
	batchDone()
	recoveredNegativeContinue()
}
