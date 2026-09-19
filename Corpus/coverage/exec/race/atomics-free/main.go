package main

import (
	"sync"
	"sync/atomic"
)

// RACE-FREE ATOMIC SHAPES (atomics arc wave 1): the detector's
// false-positive guards for the sync/atomic edges and access kinds
// (Race.lean, "sync/atomic — the per-address clocks"). Every subject
// is `go run -race` GREEN (evidence dir 2026-09-03_atomics-w1, probes)
// and must be race-free on EVERY enumerated schedule: two atomics
// never conflict (atomic↔atomic), an atomic read beside a plain read is
// two reads, and a store-release/load-acquire pair publishes plain
// data (mem#atomic: "If the effect of an atomic operation A is observed
// by atomic operation B, then A is synchronized before B").

// Two goroutines Add the same word with NO other synchronization (the
// join is a channel that carries no data): atomic↔atomic never
// conflicts. Confluent: 2 on every schedule.
func atomicVsAtomic() int {
	var n int32
	done := make(chan struct{}, 2)
	go func() { atomic.AddInt32(&n, 1); done <- struct{}{} }()
	go func() { atomic.AddInt32(&n, 1); done <- struct{}{} }()
	<-done
	<-done
	return int(atomic.LoadInt32(&n)) // 2
}

// A PLAIN read beside a concurrent atomic LOAD: read/read — no race,
// whatever the schedule (nothing writes). Confluent: 5.
func plainReadVsLoad() int {
	var n int64 = 5
	var got int64
	done := make(chan struct{})
	go func() { got = atomic.LoadInt64(&n); done <- struct{}{} }()
	r := n
	<-done
	return int(r + got) - 5 // 5
}

// MESSAGE PASSING through an atomic flag: the writer stores data (plain)
// then the flag (atomic); the reader loads the flag and reads the data
// ONLY if the flag was seen — the load acquires the store's clock, so
// the plain read is HB-after the plain write on the path where it
// happens; on the other path nothing is read. Race-free on EVERY path;
// the observation is {0, 1} (membership), the SC-excluded "flag seen,
// data stale" is absent by the same edge.
func publishAcquire() int {
	var data int64
	var flag int32
	go func() {
		data = 42
		atomic.StoreInt32(&flag, 1)
	}()
	if atomic.LoadInt32(&flag) == 1 {
		if data == 42 {
			return 1
		}
		return 100 // SC-excluded: unreachable
	}
	return 0
}

// The RMW's acquire half: an Add observing the store's value inherits
// the storer's clock, so the plain read after a successful observation
// is ordered. Race-free on every path; observation {0, 1}.
func rmwAcquire() int {
	var data int64
	var flag int32
	go func() {
		data = 7
		atomic.StoreInt32(&flag, 1)
	}()
	if atomic.AddInt32(&flag, 0) == 1 {
		return int(data) - 6 // 1
	}
	return 0
}

// A FAILED CompareAndSwap still acquires (TSan: mo_acquire on failure;
// mem#atomic: the failed CAS observed the current value, so its writer
// is synchronized before it). THE ISOLATING SHAPE (audit fix H5,
// 2026-09-03 — the first cut's `!CAS(&f,5,6) && Load(&f)==1` let the
// Load acquire and tested nothing): the reader spins on
// `CompareAndSwap(&flag, 0, 0)`, which SUCCEEDS while flag==0 and FAILS
// exactly on observing the store — the loop's exit is the failing CAS,
// and the only acquire between the writer's plain write and the
// reader's plain read is that failure's. Main is the writer and the
// spinner a child reporting through a channel (the spin row's shape),
// so the canonical schedule terminates; anti-progress schedules are
// nonterm branches. Race-free on every path; members {5}.
func casFailureAcquires() int {
	var data int64
	var flag int32
	out := make(chan int64)
	go func() {
		for atomic.CompareAndSwapInt32(&flag, 0, 0) {
		}
		out <- data
	}()
	data = 5
	atomic.StoreInt32(&flag, 1)
	return int(<-out) // 5 on every terminating path
}

// Atomics under a WaitGroup join beside a PLAIN read of a DIFFERENT word:
// sibling words are disjoint paths (the atomic op touches exactly its
// cell). Confluent.
func siblingWords() int {
	var a int64
	var b int64 = 3
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { atomic.AddInt64(&a, 4); wg.Done() }()
	r := b // a plain read of the sibling word while the child writes `a` atomically
	wg.Wait()
	return int(r + atomic.LoadInt64(&a)) // 7
}

// Typed wrappers in a struct beside a plain SIBLING field: the wrapper's
// op touches only its `v` word; the sibling is disjoint. Confluent.
type stats struct {
	hits atomic.Int64
	name string
}

func typedSiblingField() int {
	s := &stats{name: "s"}
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { s.hits.Add(2); wg.Done() }()
	n := len(s.name) // plain read of the sibling field
	wg.Wait()
	return n*10 + int(s.hits.Load()) // 12
}

func main() {
	atomicVsAtomic()
	plainReadVsLoad()
	publishAcquire()
	rmwAcquire()
	casFailureAcquires()
	siblingWords()
	typedSiblingField()
	atomicStructTagAliasFlagHandoff()
}

// BUG-111 audit F1 (C1 S2c fix round, 2026-09-19) — the `sync/atomic`
// per-address clock through two spellings of ONE word: the child publishes
// `s.x` with `StoreInt32(&s.flag, 1)`, main polls `LoadInt32(&q.flag)`
// through a struct-tag-compatible alias and reads `s.x` only on the
// observing path. mem#atomic: the store is synchronized before the load
// that observes it — through ONE address clock. Race-free (`go run -race`
// green 5/5 at GOMAXPROCS 1 and 8); a clock table keyed by the STRUCTURAL
// spelling splits the address and reports a false race on the observing
// path (main's binary at the fix round: RACE-SOME). Pins the atomic
// clock-table canonicalization. Members {0, 1}: the load may run before or
// after the store (L1 latitude); the SC-excluded stale read is absent.
type aliasAtA struct {
	flag int32
	x    int
}
type aliasAtB struct {
	flag int32
	x    int
}

func atomicStructTagAliasFlagHandoff() int {
	var s aliasAtA
	q := (*aliasAtB)(&s)
	done := make(chan int, 1)
	go func() {
		s.x = 1
		atomic.StoreInt32(&s.flag, 1)
		done <- 0
	}()
	r := 0
	if atomic.LoadInt32(&q.flag) == 1 {
		r = s.x
	}
	<-done
	return r
}
