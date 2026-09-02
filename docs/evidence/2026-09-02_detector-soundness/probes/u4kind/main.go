package main

import "sync"

// BUG-080 fix-slice probes, family U4-KIND (2026-09-02): the sync
// primitives' OWN state-word accesses, probed PRIMITIVE BY PRIMITIVE and
// in BOTH directions (a plain COPY = read, a plain OVERWRITE = write; the
// plain access in main beside the op in a child, and the roles swapped),
// plus the negative controls the fix must keep green. The gc side is
// `go build -race` of the harnessed subject (TSan's realized set, register
// #13); the machine side is the enumerator. Each subject isolates ONE
// primitive and ONE op: no plain-data race is present anywhere, so every
// red is the primitive's own words.
//
// Every copy is written to a package-level sink so the compiler cannot
// narrow `c := b; return c.x` to a single field load — the whole struct
// (the primitive's words included) is read.

type kMuBox struct {
	mu sync.Mutex
	x  int
}

type kMu2Box struct {
	mu sync.Mutex
	a  int
	b  int
}

type kMuPairBox struct {
	mu1 sync.Mutex
	mu2 sync.Mutex
	a   int
	b   int
}

type kRwBox struct {
	rw sync.RWMutex
	n  int
}

type kWgBox struct {
	wg sync.WaitGroup
	n  int
}

type kOnceBox struct {
	o sync.Once
	n int
}

var (
	kMuSink   kMuBox
	kRwSink   kRwBox
	kWgSink   kWgBox
	kOnceSink kOnceBox
)

// ---- Mutex ---------------------------------------------------------------

// MU-1 copy (main) vs Lock/Unlock (child). gc: Lock's CAS is an atomic
// write on m.state; the copy reads it plain -> RED.
func kMuCopyVsLock() int {
	var b kMuBox
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.mu.Unlock()
		done <- 0
	}()
	kMuSink = b
	<-done
	return kMuSink.x
}

// MU-2 the roles swapped: copy (child) vs Lock/Unlock (main) -> RED.
func kMuLockVsCopy() int {
	var b kMuBox
	done := make(chan int)
	go func() {
		kMuSink = b
		done <- 0
	}()
	b.mu.Lock()
	b.mu.Unlock()
	<-done
	return kMuSink.x
}

// MU-3 overwrite (main) vs Lock/Unlock (child) -> RED (the U4-1 shape).
func kMuOverwriteVsLock() int {
	var b kMuBox
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.mu.Unlock()
		done <- 0
	}()
	b = kMuBox{}
	<-done
	return b.x
}

// MU-4 copy (main) vs Unlock ONLY (child): main Locks BEFORE the spawn
// (sequenced before the child), the child performs the (legal, owner-free)
// Unlock. Isolates Unlock's atomic Add on m.state -> RED.
func kMuCopyVsUnlock() int {
	var b kMuBox
	done := make(chan int)
	b.mu.Lock()
	go func() {
		b.mu.Unlock()
		done <- 0
	}()
	kMuSink = b
	<-done
	return kMuSink.x
}

// MU-5 CONTROL: two goroutines CONTEND on one Mutex (atomic vs atomic
// never conflicts), joined before the readout -> GREEN.
func kMuContend() int {
	var b kMuBox
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.x = b.x + 1
		b.mu.Unlock()
		done <- 0
	}()
	b.mu.Lock()
	b.x = b.x + 2
	b.mu.Unlock()
	<-done
	b.mu.Lock()
	r := b.x
	b.mu.Unlock()
	return r
}

// MU-6 CONTROL: SIBLING fields written under the lock from two goroutines
// (the primitive's path `.field mu` is disjoint from `.field a`/`.field b`;
// the atomic accesses at the mutex path must not spill over the enclosing
// struct) -> GREEN.
func kMuSiblingsUnderLock() int {
	var b kMu2Box
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.a = 1
		b.mu.Unlock()
		done <- 0
	}()
	b.mu.Lock()
	b.b = 2
	b.mu.Unlock()
	<-done
	return b.a + b.b
}

// MU-7 CONTROL: two DISJOINT primitives in one struct, each guarding its
// own field, no join between the sections except the final channel ->
// GREEN.
func kMuDisjointPrims() int {
	var b kMuPairBox
	done := make(chan int)
	go func() {
		b.mu1.Lock()
		b.a = 1
		b.mu1.Unlock()
		done <- 0
	}()
	b.mu2.Lock()
	b.b = 2
	b.mu2.Unlock()
	<-done
	return b.a + b.b
}

// MU-8 CONTROL: a SIBLING-field write in main WITHOUT the lock beside the
// child's Lock/Unlock (the U4-5 `disjoint-field-vs-lock` control, kept) ->
// GREEN.
func kMuSiblingBesideLock() int {
	var b kMuBox
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.mu.Unlock()
		done <- 0
	}()
	b.x = 7
	<-done
	return b.x
}

// ---- RWMutex -------------------------------------------------------------
// gc (go1.26.5 sync/rwmutex.go): EVERY RWMutex op begins with
// `race.Read(unsafe.Pointer(&rw.w))` — a PLAIN read — and then runs its
// readerCount/readerWait atomics and the embedded Mutex's CAS under
// `race.Disable()`, which in Go's TSan integration routes sync/atomic ops
// to the un-instrumented NoTsanAtomic path. So TSan's realized set for an
// RWMutex op is ONE PLAIN READ of the primitive: read/read with a copy
// (GREEN), read/write with an overwrite (RED).

// RW-1 copy vs RLock/RUnlock -> GREEN (read/read).
func kRwCopyVsRLock() int {
	var r kRwBox
	done := make(chan int)
	go func() {
		r.rw.RLock()
		r.rw.RUnlock()
		done <- 0
	}()
	kRwSink = r
	<-done
	return kRwSink.n
}

// RW-2 overwrite vs RLock/RUnlock -> RED (the U4-3 shape).
func kRwOverwriteVsRLock() int {
	var r kRwBox
	done := make(chan int)
	go func() {
		r.rw.RLock()
		r.rw.RUnlock()
		done <- 0
	}()
	r = kRwBox{}
	<-done
	return r.n
}

// RW-3 copy vs Lock/Unlock (the WRITE lock) -> GREEN (read/read).
func kRwCopyVsLock() int {
	var r kRwBox
	done := make(chan int)
	go func() {
		r.rw.Lock()
		r.rw.Unlock()
		done <- 0
	}()
	kRwSink = r
	<-done
	return kRwSink.n
}

// RW-4 overwrite vs Lock/Unlock -> RED.
func kRwOverwriteVsLock() int {
	var r kRwBox
	done := make(chan int)
	go func() {
		r.rw.Lock()
		r.rw.Unlock()
		done <- 0
	}()
	r = kRwBox{}
	<-done
	return r.n
}

// RW-5 the roles swapped: overwrite (child) vs RLock/RUnlock (main) -> RED.
func kRwRLockVsOverwrite() int {
	var r kRwBox
	done := make(chan int)
	go func() {
		r = kRwBox{}
		done <- 0
	}()
	r.rw.RLock()
	r.rw.RUnlock()
	<-done
	return r.n
}

// RW-6 overwrite vs RUnlock ONLY (main RLocks before the spawn; the child
// RUnlocks) -> RED (RUnlock's plain read of rw.w).
func kRwOverwriteVsRUnlock() int {
	var r kRwBox
	done := make(chan int)
	r.rw.RLock()
	go func() {
		r.rw.RUnlock()
		done <- 0
	}()
	r = kRwBox{}
	<-done
	return r.n
}

// RW-7 overwrite vs Unlock ONLY (main Locks before the spawn; the child
// Unlocks) -> RED.
func kRwOverwriteVsUnlock() int {
	var r kRwBox
	done := make(chan int)
	r.rw.Lock()
	go func() {
		r.rw.Unlock()
		done <- 0
	}()
	r = kRwBox{}
	<-done
	return r.n
}

// RW-8 CONTROL: a reader and a writer CONTEND, joined before the readout
// -> GREEN.
func kRwContend() int {
	var r kRwBox
	done := make(chan int)
	go func() {
		r.rw.RLock()
		_ = r.n
		r.rw.RUnlock()
		done <- 0
	}()
	r.rw.Lock()
	r.n = 5
	r.rw.Unlock()
	<-done
	r.rw.RLock()
	v := r.n
	r.rw.RUnlock()
	return v
}

// ---- WaitGroup -----------------------------------------------------------
// gc (go1.26.5 sync/waitgroup.go): the state word's atomics run under
// `race.Disable()` (invisible to TSan); the ONLY instrumented accesses are
// the misuse pair on `wg.sema` — a PLAIN READ when an Add takes the counter
// off 0 upward (:111-115), a PLAIN WRITE when the FIRST waiter registers
// (:185-190). Done, Add from a nonzero counter, and a Wait that returns at
// counter 0 touch nothing TSan sees.

// WG-1 copy vs Add(1) from 0 / Done -> GREEN (read/read).
func kWgCopyVsAddFrom0() int {
	var w kWgBox
	done := make(chan int)
	go func() {
		w.wg.Add(1)
		w.wg.Done()
		done <- 0
	}()
	kWgSink = w
	<-done
	return kWgSink.n
}

// WG-2 overwrite vs Add(1) from 0 / Done -> RED (the U4-2 shape; the sema
// read vs the overwrite).
func kWgOverwriteVsAddFrom0() int {
	var w kWgBox
	done := make(chan int)
	go func() {
		w.wg.Add(1)
		w.wg.Done()
		done <- 0
	}()
	w = kWgBox{}
	<-done
	return w.n
}

// WG-3 copy vs Done ONLY (main Adds before the spawn) -> GREEN.
func kWgCopyVsDone() int {
	var w kWgBox
	done := make(chan int)
	w.wg.Add(1)
	go func() {
		w.wg.Done()
		done <- 0
	}()
	kWgSink = w
	<-done
	return kWgSink.n
}

// WG-4 overwrite vs Done ONLY (main Adds before the spawn) -> GREEN in gc:
// Done performs NO instrumented access (its state Add is under
// race.Disable). The program is racy by mem#model (a non-atomic
// write beside an atomic RMW) but TSan — the racy lane's oracle — does not
// see it; recorded as the WaitGroup alignment fact, not a pin.
func kWgOverwriteVsDone() int {
	var w kWgBox
	done := make(chan int)
	w.wg.Add(1)
	go func() {
		w.wg.Done()
		done <- 0
	}()
	w = kWgBox{}
	<-done
	return w.n
}

// WG-5 copy (child) vs a BLOCKING Wait that is the FIRST waiter (main Adds
// before the spawn, then Waits; the child copies, then Dones) -> RED (the
// first waiter's sema WRITE vs the copy's read; the write precedes main's
// acquire, the copy precedes the child's release — HB-unordered). Roles
// were the other way round in the first cut; the 5-run sampler then never
// realized a schedule where the Wait blocked (main's Done landed first and
// a Wait at counter 0 registers nothing), so it read agree-DRF for a
// sampler reason — the shape here makes the blocking Wait certain.
func kWgCopyVsFirstWait() int {
	var w kWgBox
	w.wg.Add(1)
	go func() {
		kWgSink = w
		w.wg.Done()
	}()
	w.wg.Wait()
	return kWgSink.n
}

// WG-6 overwrite vs a Wait that returns at counter 0 -> GREEN (nothing
// instrumented on that path).
func kWgOverwriteVsWaitAt0() int {
	var w kWgBox
	done := make(chan int)
	go func() {
		w.wg.Wait()
		done <- 0
	}()
	w = kWgBox{}
	<-done
	return w.n
}

// ---- Once ----------------------------------------------------------------
// gc (go1.26.5 sync/once.go, no race.Disable anywhere): Do begins with an
// ATOMIC LOAD of o.done; a not-yet-done Do takes doSlow, whose o.m.Lock()
// is the Mutex's atomic CAS (visible), then o.done.Store(true) and
// o.m.Unlock() (atomic writes). A Do that observes done is the atomic
// READ alone.

// ONCE-1 copy vs the FIRST Do -> RED (the CAS/Store atomic writes vs the
// copy's read).
func kOnceCopyVsFirstDo() int {
	var o kOnceBox
	done := make(chan int)
	go func() {
		o.o.Do(func() {})
		done <- 0
	}()
	kOnceSink = o
	<-done
	return kOnceSink.n
}

// ONCE-2 overwrite vs the FIRST Do -> RED (the U4-4 shape).
func kOnceOverwriteVsFirstDo() int {
	var o kOnceBox
	done := make(chan int)
	go func() {
		o.o.Do(func() {})
		done <- 0
	}()
	o = kOnceBox{}
	<-done
	return o.n
}

// ONCE-3 copy vs a Do AFTER completion (main Does before the spawn; the
// child's Do observes done — an atomic READ only) -> GREEN (read/read).
func kOnceCopyVsDoneDo() int {
	var o kOnceBox
	done := make(chan int)
	o.o.Do(func() {})
	go func() {
		o.o.Do(func() {})
		done <- 0
	}()
	kOnceSink = o
	<-done
	return kOnceSink.n
}

// ONCE-4 overwrite vs a Do AFTER completion -> RED (the atomic read vs the
// plain write).
func kOnceOverwriteVsDoneDo() int {
	var o kOnceBox
	done := make(chan int)
	o.o.Do(func() {})
	go func() {
		o.o.Do(func() {})
		done <- 0
	}()
	o = kOnceBox{}
	<-done
	return o.n
}

// ONCE-5 the roles swapped: copy (child) vs the FIRST Do (main) -> RED.
func kOnceFirstDoVsCopy() int {
	var o kOnceBox
	done := make(chan int)
	go func() {
		kOnceSink = o
		done <- 0
	}()
	o.o.Do(func() {})
	<-done
	return kOnceSink.n
}

// ONCE-6 CONTROL: two goroutines CONTEND on one Do, joined -> GREEN.
func kOnceContend() int {
	var o kOnceBox
	done := make(chan int)
	go func() {
		o.o.Do(func() { o.n = 42 })
		done <- 0
	}()
	o.o.Do(func() { o.n = 42 })
	<-done
	return o.n
}

func main() {
	println(kMuCopyVsLock(), kMuLockVsCopy(), kMuOverwriteVsLock(), kMuCopyVsUnlock(),
		kMuContend(), kMuSiblingsUnderLock(), kMuDisjointPrims(), kMuSiblingBesideLock())
	println(kRwCopyVsRLock(), kRwOverwriteVsRLock(), kRwCopyVsLock(), kRwOverwriteVsLock(),
		kRwRLockVsOverwrite(), kRwOverwriteVsRUnlock(), kRwOverwriteVsUnlock(), kRwContend())
	println(kWgCopyVsAddFrom0(), kWgOverwriteVsAddFrom0(), kWgCopyVsDone(), kWgOverwriteVsDone(),
		kWgCopyVsFirstWait(), kWgOverwriteVsWaitAt0())
	println(kOnceCopyVsFirstDo(), kOnceOverwriteVsFirstDo(), kOnceCopyVsDoneDo(),
		kOnceOverwriteVsDoneDo(), kOnceFirstDoVsCopy(), kOnceContend())
}
