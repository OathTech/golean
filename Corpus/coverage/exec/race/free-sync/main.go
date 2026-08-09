package main

import "sync"

// FALSE-POSITIVE guards for the SYNC-package HB edges (spec-parity
// slice 2, design note §5): each subject is race-free exactly through
// one sync edge — a detector that missed the edge would refuse on some
// schedule and break the certified singleton. go run -race verified
// green (probes p15/p16/p17's shapes).

var freeSyncX int

// The Mutex edge (unlock n synchronizes-before lock m, n < m): both
// accesses under the lock, joined before the readout.
func freeSyncMutex() int {
	freeSyncX = 0
	var m sync.Mutex
	done := make(chan int)
	go func() {
		m.Lock()
		freeSyncX = freeSyncX + 1
		m.Unlock()
		done <- 1
	}()
	m.Lock()
	freeSyncX = freeSyncX + 2
	m.Unlock()
	<-done
	m.Lock()
	r := freeSyncX
	m.Unlock()
	return r
}

// The WaitGroup edge (Done synchronizes-before the Wait it unblocks):
// the unsynchronized-looking write/read pair is ordered by Done→Wait.
func freeSyncWgEdge() int {
	freeSyncX = 0
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		freeSyncX = 42
		wg.Done()
	}()
	wg.Wait()
	return freeSyncX
}

// The Once edge (the return from f synchronizes-before the return from
// any Do): both goroutines call Do; whichever runs f, the other's Do
// return acquires f's completion, ordering the write before both
// readouts.
func freeSyncOnceEdge() int {
	freeSyncX = 0
	var o sync.Once
	done := make(chan int)
	go func() {
		o.Do(func() { freeSyncX = 42 })
		done <- freeSyncX
	}()
	o.Do(func() { freeSyncX = 42 })
	r := freeSyncX
	<-done
	return r
}

// Serialized WRITE-lock sections on an RWMutex: the write-unlock →
// write-lock edge (semA) orders the two increments whichever order the
// schedule realizes — the green twin of negative-sync's
// raceSyncRlockSerialized (readers get NO such edge).
func freeSyncRwWriters() int {
	freeSyncX = 0
	var m sync.RWMutex
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		m.Lock()
		freeSyncX = freeSyncX + 1
		m.Unlock()
		wg.Done()
	}()
	go func() {
		m.Lock()
		freeSyncX = freeSyncX + 1
		m.Unlock()
		wg.Done()
	}()
	wg.Wait()
	return freeSyncX
}

func main() {
	freeSyncMutex()
	freeSyncWgEdge()
	freeSyncOnceEdge()
	freeSyncRwWriters()
}
