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

// BUG-080 (U4, born-FAIL pins 2026-09-02 — the detector-soundness
// differential's third-cell finding): gc's -race build instruments the
// sync primitive's OWN state words — Mutex.Lock's CAS on m.state is an
// atomic write, WaitGroup.Add reads its state word (`runtime.raceread`)
// — so a plain access to a primitive IN USE by another goroutine is a
// data race by mem#restrictions (non-atomic beside atomic) and TSan-red
// (10/10 runs at GOMAXPROCS 1 and 8). The machine records NO access for
// a sync op (Race.lean U4), so these racy programs run to a value: the
// racy lane's every-path-refuses claim FAILS here until the atomic
// access kind lands (Q-ATOMIC owner proposal §4 — the fix is that kind,
// not a table entry: recording sync ops as plain writes would make two
// legal contending Locks conflict).

type raceSyncWgBox struct {
	wg sync.WaitGroup
	n  int
}

// Whole-struct overwrite of a struct holding a WaitGroup while the
// child Adds/Dones on it: TSan "Read … runtime.raceread" (Add) vs the
// overwrite. Members the machine sees: ok, or the negative-counter
// panic when the overwrite lands between Add and Done — never race.
func raceSyncWgOverwrite() int {
	var w raceSyncWgBox
	done := make(chan int)
	go func() {
		w.wg.Add(1)
		w.wg.Done()
		done <- 0
	}()
	w = raceSyncWgBox{}
	<-done
	return w.n
}

type raceSyncMuBox struct {
	mu sync.Mutex
	x  int
}

// Copy of a struct holding a Mutex while the child locks it: TSan
// "Write … sync/atomic.CompareAndSwapInt32" (Lock) vs the copy's read.
// The machine's copy carries state gc-faithfully (sync design §3) and
// records a plain read of the struct cell only — no conflicting access
// is recorded for the Lock, so the run completes with a value.
func raceSyncMutexCopy() int {
	var b raceSyncMuBox
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.mu.Unlock()
		done <- 0
	}()
	c := b
	<-done
	return c.x
}

func main() {
	raceSyncOneSide()
	raceSyncRlockSerialized()
	raceSyncWgNoEdge()
	raceSyncWgOverwrite()
	raceSyncMutexCopy()
}
