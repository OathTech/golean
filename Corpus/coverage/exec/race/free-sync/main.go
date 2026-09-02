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

// BUG-080 CONTROLS (the atomic access-kind slice, 2026-09-02): the
// detector now records each sync op's access on the primitive's OWN
// path (Race.lean `syncEntryKinds`), so the ruling's check (i) — one
// syncData cell per primitive vs the path-overlap relation — needs green
// guards: plain accesses to SIBLING fields of the struct holding the
// primitive, and to other primitives in the same struct, must stay
// disjoint from it. go run -race green (probes/u4kind mu-siblings-under-
// lock / mu-disjoint-prims, 5/5 at GOMAXPROCS 1 and 8).

type freeSyncSiblingBox struct {
	mu sync.Mutex
	a  int
	b  int
}

// Sibling fields written under the lock from two goroutines: the two
// Locks' atomic writes land at `.field mu` (atomic↔atomic never
// conflicts); the field writes at `.field a` / `.field b` are disjoint
// from the mutex path and from each other.
func freeSyncMutexSiblings() int {
	var s freeSyncSiblingBox
	done := make(chan int)
	go func() {
		s.mu.Lock()
		s.a = 1
		s.mu.Unlock()
		done <- 0
	}()
	s.mu.Lock()
	s.b = 2
	s.mu.Unlock()
	<-done
	return s.a + s.b
}

type freeSyncPairBox struct {
	mu1 sync.Mutex
	mu2 sync.Mutex
	a   int
	b   int
}

// Two DISJOINT primitives in one struct, each guarding its own field:
// the ops' accesses sit at `.field mu1` / `.field mu2` — distinct paths
// — and nothing overlaps.
func freeSyncDisjointPrims() int {
	var s freeSyncPairBox
	done := make(chan int)
	go func() {
		s.mu1.Lock()
		s.a = 1
		s.mu1.Unlock()
		done <- 0
	}()
	s.mu2.Lock()
	s.b = 2
	s.mu2.Unlock()
	<-done
	return s.a + s.b
}

func main() {
	freeSyncMutex()
	freeSyncWgEdge()
	freeSyncOnceEdge()
	freeSyncRwWriters()
	freeSyncMutexSiblings()
	freeSyncDisjointPrims()
}
