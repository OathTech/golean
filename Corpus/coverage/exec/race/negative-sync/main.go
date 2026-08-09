package main

import "sync"

// RACY-NEGATIVE lane, SYNC-package shapes (spec-parity slice 2): every
// subject races on EVERY interleaving — the sync ops present do NOT
// order the conflicting pair — so every enumerated path must refuse,
// with `go run -race` as the justifying oracle.

var negSyncX int

// One-sided locking: the worker writes under the mutex, main reads
// with no lock. Main's read and the worker's write are HB-unordered on
// every schedule (main's <-done join is AFTER the read); both accesses
// execute on every complete path.
func raceSyncOneSide() int {
	negSyncX = 0
	var m sync.Mutex
	done := make(chan int)
	go func() {
		m.Lock()
		negSyncX = 1
		m.Unlock()
		done <- 1
	}()
	r := negSyncX
	<-done
	return r
}

// Two readers WRITING under read locks (probe p14): RLock/RUnlock give
// readers no mutual HB edge — the memory-model text orders RUnlock
// only before the NEXT WRITE lock — so the two increments race even
// when a schedule serializes them perfectly. This is the two-clock
// discriminator: a single-clock model would order serialized readers
// and admit a value leaf on those paths.
func raceSyncRlockSerialized() int {
	negSyncX = 0
	var m sync.RWMutex
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		m.RLock()
		negSyncX = negSyncX + 1
		m.RUnlock()
		wg.Done()
	}()
	go func() {
		m.RLock()
		negSyncX = negSyncX + 1
		m.RUnlock()
		wg.Done()
	}()
	wg.Wait()
	return negSyncX
}

// A WaitGroup PRESENT but ordering nothing: the counter is already 0,
// so the worker's Wait returns immediately having acquired no Done
// release — the write/read pair is bare on every schedule.
func raceSyncWgNoEdge() int {
	negSyncX = 0
	var wg sync.WaitGroup
	done := make(chan int)
	go func() {
		wg.Wait()
		negSyncX = 1
		done <- 1
	}()
	r := negSyncX
	<-done
	return r
}

func main() {
	raceSyncOneSide()
	raceSyncRlockSerialized()
	raceSyncWgNoEdge()
}
