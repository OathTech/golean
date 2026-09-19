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
// goroutine is a data race by mem#model (non-atomic beside
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

// Q-TRYLOCK (2026-09-03): a plain overwrite of an UNLOCKED Mutex
// unordered with a TryLock on it. gc -race: the TryLock's state CAS is an
// atomic write against the plain overwrite — RACE 20/20 at GOMAXPROCS 1
// and 8 (docs/evidence/2026-09-03_q-trylock/, probe muOverwriteVsTryLock).
// The machine records `.atomicWrite @state` on BOTH envelope members
// (the lost CAS is gc's realization of the spurious false), so every path
// refuses. Both accesses execute on every complete path.
func raceSyncOverwriteVsTryLock() int {
	var m sync.Mutex
	c1, c2 := make(chan int), make(chan int)
	go func() { _ = m.TryLock(); c1 <- 1 }()
	go func() { m = sync.Mutex{}; c2 <- 1 }()
	return <-c1 + <-c2
}

// Q-TRYLOCK (2026-09-03): "An unsuccessful call has no synchronizing
// effect at all" (mem#locks). The worker holds the lock across main's
// TryLock (channel-ordered), so the TryLock is FORCED false (bound 1, no
// pick, nothing recorded, NO acquire); main's plain read of negSyncX is
// then unordered with the worker's write after `release` — the join is
// AFTER the read. gc -race RACE 20/20 (probe muFailedTryLockNoEdge); a
// detector that let the failed call acquire would run this to a value.
func raceSyncFailedTryLockNoEdge() int {
	negSyncX = 0
	var m sync.Mutex
	held := make(chan int)
	release := make(chan int)
	done := make(chan int)
	go func() {
		m.Lock()
		held <- 1
		<-release
		negSyncX = 9
		m.Unlock()
		done <- 1
	}()
	<-held
	ok := m.TryLock()
	release <- 1
	v := negSyncX
	<-done
	if ok {
		return -1
	}
	return v
}

func main() {
	raceSyncOneSide()
	raceSyncRlockSerialized()
	raceSyncWgNoEdge()
	raceSyncWgOverwrite()
	raceSyncMutexCopy()
	raceSyncRwOverwrite()
	raceSyncOnceCopy()
	raceSyncStructTagAliasNestedMutexCopy()
	raceSyncStructTagAliasNestedWgOverwrite()
	raceSyncNestedMutexCopy()
}

// BUG-111 audit F1 (C1 S2c fix round, 2026-09-19): a NESTED Mutex through a
// struct-tag-compatible alias — the `.syncWord` key (Lock's state CAS at
// `q.in.mu`, an atomic write) vs the `.data` key of the copy `t := o.in`
// (a plain read at a FIELD path). BUG-080's copy-beside-Lock class AND
// BUG-111's alias in one program: `go run -race` RACE 5/5 at GOMAXPROCS 1
// and 8. Structural keys MISS it — the sync word's path `.field (.field o
// aliasNestOutB "in") aliasNestIn "mu"` is not prefixed by the copy's
// `.field o aliasNestOutA "in"` (the typeIds differ at the `in` step) — so
// main's binary at the fix round ACCEPTED it on every enumerated path (a
// HOLE); with the sync words canonicalized the copy's path IS a prefix and
// every path refuses. Born PASS under the fix; pins the `.syncWord`
// canonicalization (the part of fix (i) beyond the ruling's `.data` letter).
type aliasNestIn struct {
	mu sync.Mutex
	f  int
}
type aliasNestOutA struct {
	in aliasNestIn
	g  int
}
type aliasNestOutB struct {
	in aliasNestIn
	g  int
}

func raceSyncStructTagAliasNestedMutexCopy() int {
	var o aliasNestOutA
	q := (*aliasNestOutB)(&o)
	done := make(chan int, 1)
	go func() {
		q.in.mu.Lock()
		q.in.f = 1
		q.in.mu.Unlock()
		done <- 0
	}()
	t := o.in
	<-done
	return t.f + o.in.f
}

// BUG-111 audit F1 (C1 S2c fix round, 2026-09-19), RESHAPED to race on EVERY
// schedule: the WaitGroup `sema` word through a NESTED alias. The audit's
// litmus (`wgAliasNestedCopyBesideWait`: a copy of the nested struct beside
// a parked Wait's first-waiter sema WRITE) is racy only on the schedules
// where the waiter parks before the Done (RACE-SOME; gc's sampler 0/5 —
// waitgroup.go:190 races in that schedule) and no lane pins a RACE-SOME
// program honestly, so this row races the SAME word on every path: the
// child's `Add(1)` from counter 0 through the alias performs gc's realized
// `race.Read(&wg.sema)` (waitgroup.go:115 — the BUG-080 `wg-overwrite` pin's
// access, here at a FIELD path), main OVERWRITES the nested struct. Both
// accesses execute on every path and are HB-unordered (the join follows the
// overwrite). Structural keys miss it (main's binary ACCEPTS); the canonical
// sync-word path is prefixed by the overwrite's canonical path — refused.
type aliasWgIn struct {
	wg sync.WaitGroup
	f  int
}
type aliasWgOutA struct {
	in aliasWgIn
	g  int
}
type aliasWgOutB struct {
	in aliasWgIn
	g  int
}

func raceSyncStructTagAliasNestedWgOverwrite() int {
	var o aliasWgOutA
	q := (*aliasWgOutB)(&o)
	done := make(chan int, 1)
	go func() {
		q.in.wg.Add(1)
		q.in.wg.Done()
		done <- 0
	}()
	o.in = aliasWgIn{}
	<-done
	return o.in.f
}

// BUG-080's class at a FIELD path — NO alias (the C1 S2c audit's F3,
// 2026-09-19): a copy of a NESTED struct holding a Mutex beside another
// goroutine's Lock on it. `go run -race` RACE 5/5. The tracked BUG-080 pins
// copy ROOT variables (`c := b`), whose `.base` key is a prefix of every
// path whatever the typeIds — they could not have distinguished a
// `.data`-only canonicalization from the landed every-emitter one; THIS
// class could: with the sync words left structural, the copy's canonical
// key `.field o $canon "in"` would no longer prefix `.field (.field o
// nestedMuOut "in") nestedMuIn "mu"` and the race would be MISSED. Both
// binaries refuse (born PASS); the must-stay-red guard of the sync-word
// canonicalization (BUG-111 fix (i) at every emitter).
type nestedMuIn struct {
	mu sync.Mutex
	f  int
}
type nestedMuOut struct {
	in nestedMuIn
	g  int
}

func raceSyncNestedMutexCopy() int {
	var o nestedMuOut
	done := make(chan int, 1)
	go func() {
		o.in.mu.Lock()
		o.in.f = 1
		o.in.mu.Unlock()
		done <- 0
	}()
	t := o.in
	<-done
	return t.f + o.in.f
}
