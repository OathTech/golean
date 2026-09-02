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

// BUG-080 (U4 — born-FAIL pinned 2026-09-02 by the detector-soundness
// differential's third-cell finding, FIXED the same day by the atomic
// access-kind slice): gc's -race build realizes accesses on the sync
// primitive's OWN words — Mutex.Lock's CAS on m.state is an atomic
// write, WaitGroup.Add's first increment reads wg.sema (a plain read),
// every RWMutex op reads rw.w (`race.Read`), Once.Do's slow path takes
// the atomic CAS — so a plain access to a primitive IN USE by another
// goroutine is a data race by mem#restrictions (non-atomic beside
// atomic) and TSan-red (10/10 runs at GOMAXPROCS 1 and 8). The machine
// used to record NO access for a sync op, so these programs ran to a
// value; since the fix `raceUpdate`'s sync arm records TSan's realized
// per-op set at the primitive's own path with a KIND (Race.lean
// `AccessKind`: atomic↔atomic never conflicts, so contending ops stay
// green; atomic↔plain conflicts unless both are reads), and every path
// of these subjects refuses. Per-primitive derivation and the
// two-direction probe evidence: Race.lean's "sync primitives' OWN state
// words" section; docs/evidence/2026-09-02_detector-soundness/probes/u4kind.

type raceSyncWgBox struct {
	wg sync.WaitGroup
	n  int
}

// Whole-struct overwrite of a struct holding a WaitGroup while the
// child Adds/Dones on it: TSan "Read … runtime.raceread" (Add's first
// increment reads wg.sema) vs the overwrite. The machine records that
// read (plain) at the wg's path; the overwrite of the enclosing struct
// overlaps it on every schedule — refused before any member could
// reach the negative-counter panic.
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
// The machine records Lock's atomic write at the mutex's path; the
// copy's plain read of the enclosing struct overlaps it — refused on
// every schedule (an atomic write conflicts with a plain read).
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

type raceSyncRwBox struct {
	rw sync.RWMutex
	n  int
}

// Whole-struct overwrite of a struct holding an RWMutex while the child
// RLocks/RUnlocks it. gc: every RWMutex op opens with
// `race.Read(&rw.w)` — a PLAIN read (the counters run under
// race.Disable) — so the overwrite is TSan-red where a COPY would be
// read/read green (the probe family's rw-copy rows). The machine
// records the plain read at the rw's path; the overwrite overlaps it on
// every schedule — refused before the overwritten RUnlock could turn
// fatal.
func raceSyncRwOverwrite() int {
	var r raceSyncRwBox
	done := make(chan int)
	go func() {
		r.rw.RLock()
		r.rw.RUnlock()
		done <- 0
	}()
	r = raceSyncRwBox{}
	<-done
	return r.n
}

type raceSyncOnceBox struct {
	o sync.Once
	n int
}

// Copy of a struct holding a Once while the child performs the FIRST
// Do on it: gc's doSlow takes o.m.Lock() (an atomic CAS) and Stores
// o.done — atomic writes the copy's plain read races with. (A Do that
// observes completion is an atomic READ alone, green beside a copy —
// the probe family's once-copy-vs-done-do row.) The machine records
// the atomic write at the Once's path; the copy overlaps it on every
// schedule.
func raceSyncOnceCopy() int {
	var o raceSyncOnceBox
	done := make(chan int)
	go func() {
		o.o.Do(func() {})
		done <- 0
	}()
	c := o
	<-done
	return c.n
}

func main() {
	raceSyncOneSide()
	raceSyncRlockSerialized()
	raceSyncWgNoEdge()
	raceSyncWgOverwrite()
	raceSyncMutexCopy()
	raceSyncRwOverwrite()
	raceSyncOnceCopy()
}
