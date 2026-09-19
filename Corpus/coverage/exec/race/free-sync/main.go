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

// Q-U4RESIDUAL (A) guards (2026-09-02): a plain COPY beside an RWMutex
// LOCK op ALONE is NOT a data race — mem#model lists mutex lock as
// read-like and a copy is read-like, so there is no write-like operand
// (the ruling's own statement of what is NOT in the refused class). The
// shape isolates the lock op: the child locks, then WAITS for main's ack
// before unlocking, so main's copy is HB-before the (write-like) unlock
// and unordered only with the lock. gc -race green (TSan: read/read on
// rw.w); the machine records `.atomicRead` for the lock (Race.lean
// `syncEntryKinds`) — read-like beside the copy's plain read, no
// conflict — and the unlock's `.atomicWrite` is HB-after the copy.
// A detector that keyed the lock op write-like would refuse here.

type freeSyncRwBox struct {
	rw sync.RWMutex
	n  int
}

var freeSyncRwSink freeSyncRwBox

func freeSyncRwCopyBesideRLock() int {
	var r freeSyncRwBox
	ack := make(chan int)
	done := make(chan int)
	go func() {
		r.rw.RLock()
		<-ack
		r.rw.RUnlock()
		done <- 0
	}()
	freeSyncRwSink = r
	ack <- 0
	<-done
	return freeSyncRwSink.n
}

func freeSyncRwCopyBesideLock() int {
	var r freeSyncRwBox
	ack := make(chan int)
	done := make(chan int)
	go func() {
		r.rw.Lock()
		<-ack
		r.rw.Unlock()
		done <- 0
	}()
	freeSyncRwSink = r
	ack <- 0
	<-done
	return freeSyncRwSink.n
}

// Q-TRYLOCK (2026-09-03): a write under a SUCCESSFUL TryLock, read under
// Lock elsewhere after the Unlock — "A successful call to l.TryLock is
// equivalent to a call to l.Lock" (mem#locks): the Unlock→Lock edge
// orders the pair. The spurious member falls back to Lock, so the
// critical section runs on every schedule: singleton {5}. gc -race green
// 20/20 (probe muDrfTryLockPublish).
func freeSyncTryLockPublish() int {
	freeSyncX = 0
	var m sync.Mutex
	done := make(chan int)
	if !m.TryLock() {
		m.Lock()
	}
	freeSyncX = 5
	m.Unlock()
	go func() {
		m.Lock()
		v := freeSyncX
		m.Unlock()
		done <- v
	}()
	return <-done
}

// Q-TRYLOCK (2026-09-03), RWMutex: the writer's TryLock (fallback Lock)
// publishes; the reader acquires under RLock after the Unlock. Singleton
// {6}; gc -race green 20/20 (probe rwDrfTryLockPublish).
func freeSyncRwTryLockPublish() int {
	freeSyncX = 0
	var rw sync.RWMutex
	done := make(chan int)
	if !rw.TryLock() {
		rw.Lock()
	}
	freeSyncX = 6
	rw.Unlock()
	go func() {
		rw.RLock()
		v := freeSyncX
		rw.RUnlock()
		done <- v
	}()
	return <-done
}

// Q-TRYLOCK (2026-09-03), RWMutex TryRLock as the ACQUIRING side: the
// writer goroutine writes under Lock; main reads under TryRLock (fallback
// RLock while the writer holds). Either order is DRF — reader first:
// RUnlock synchronizes before the writer's Lock return (mem#locks' RLock
// rule); writer first: Unlock synchronizes before the TryRLock/RLock
// return — so the value is schedule latitude {0, 8} and no path refuses.
// gc -race green 20/20 (probe rwDrfTryRLockAcquire's edge).
func freeSyncRwTryRLockAcquire() int {
	freeSyncX = 0
	var rw sync.RWMutex
	done := make(chan int)
	go func() {
		rw.Lock()
		freeSyncX = 8
		rw.Unlock()
		done <- 1
	}()
	if !rw.TryRLock() {
		rw.RLock()
	}
	v := freeSyncX
	rw.RUnlock()
	<-done
	return v
}

func main() {
	freeSyncMutex()
	freeSyncWgEdge()
	freeSyncOnceEdge()
	freeSyncRwWriters()
	freeSyncMutexSiblings()
	freeSyncDisjointPrims()
	freeSyncRwCopyBesideRLock()
	freeSyncRwCopyBesideLock()
	freeSyncStructTagAliasMutexHandoff()
	freeSyncStructTagAliasRwHandoff()
	freeSyncStructTagAliasOnceObserve()
}

// BUG-111 audit F1 (C1 S2c fix round, 2026-09-19) — the FALSE-RACE
// direction: ONE Mutex, two spellings. The child locks `q.mu`, main locks
// `s.mu` — the same word through a struct-tag-compatible alias — and both
// write `s.x` under it. The HB edge (mem#locks: unlock n synchronizes
// before lock m, n < m) runs through the ONE clock, so the program is
// race-free (`go run -race` green 5/5 at GOMAXPROCS 1 and 8); a clock table
// keyed by the STRUCTURAL spelling splits the mutex into two clocks and
// reports a false race (main's binary at the fix round: RACE-ALL on every
// enumerated path). Pins the `HbAction` clock-table canonicalization. Which
// critical section runs first is L1 latitude: members {1, 2}.
type aliasMuHA struct {
	mu sync.Mutex
	x  int
}
type aliasMuHB struct {
	mu sync.Mutex
	x  int
}

func freeSyncStructTagAliasMutexHandoff() int {
	var s aliasMuHA
	q := (*aliasMuHB)(&s)
	done := make(chan int, 1)
	go func() {
		q.mu.Lock()
		s.x = 2
		q.mu.Unlock()
		done <- 0
	}()
	s.mu.Lock()
	s.x = 1
	s.mu.Unlock()
	<-done
	return s.x
}

// BUG-111 audit F1 — the RWMutex clock PAIR through two spellings: the
// writer under `q.mu.Lock`, the reader under `s.mu.RLock`. Race-free (gc
// green); main's binary reported a false race on every path (the two
// spellings split the writer/reader clocks). The readout after the join is
// the child's write: singleton {2}.
type aliasRwHA struct {
	mu sync.RWMutex
	x  int
}
type aliasRwHB struct {
	mu sync.RWMutex
	x  int
}

func freeSyncStructTagAliasRwHandoff() int {
	var s aliasRwHA
	q := (*aliasRwHB)(&s)
	done := make(chan int, 1)
	go func() {
		q.mu.Lock()
		s.x = 2
		q.mu.Unlock()
		done <- 0
	}()
	s.mu.RLock()
	_ = s.x
	s.mu.RUnlock()
	<-done
	return s.x
}

// BUG-111 audit F1 — the Once clock through two spellings: `q.o.Do` in the
// child, `s.o.Do` in main, the observer's read of `s.x` ordered by the
// completion edge (mem#more: the completion of f() "is synchronized before
// the return of any call of once.Do(f)"). Race-free (gc green); main's
// binary reported a false race on some paths (a split Once clock). Singleton
// {1} — f runs once whichever Do begins it.
type aliasOnceA struct {
	o sync.Once
	x int
}
type aliasOnceB struct {
	o sync.Once
	x int
}

func freeSyncStructTagAliasOnceObserve() int {
	var s aliasOnceA
	q := (*aliasOnceB)(&s)
	done := make(chan int, 1)
	go func() {
		q.o.Do(func() { s.x = 1 })
		done <- 0
	}()
	s.o.Do(func() { s.x = 1 })
	_ = s.x
	<-done
	return s.x
}
