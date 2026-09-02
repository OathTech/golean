package main

import "sync"

// Q-U4RESIDUAL option (A) probes, family U4-GOMEM (2026-09-02): the two
// shapes the BUG-080 family `probes/u4kind` left UNPROBED — a plain COPY
// beside RWMutex `RUnlock` and beside `Unlock` — plus two controls the
// ruling's table must keep green. The gc side is `go build -race` of the
// harnessed subject (TSan's realized set, register #13), 20 runs at each
// GOMAXPROCS value; the machine side is the enumerator. Expected cells
// are stated per subject.
//
// Every copy lands in a package-level sink so the compiler cannot narrow
// the struct read to one field.

type gRwBox struct {
	rw sync.RWMutex
	n  int
}

type gWgBox struct {
	wg sync.WaitGroup
	n  int
}

var (
	gRwSink gRwBox
	gWgSink gWgBox
)

// G-1 copy (main) beside RUnlock ONLY (main RLocks before the spawn; the
// child RUnlocks). go_mem: unlock is write-like, the copy a plain read ->
// data race -> machine REFUSES. TSan: RUnlock's only instrumented access
// is the plain race.Read(&rw.w) -> read/read -> gc GREEN. Expected cell:
// over-refusal BY DESIGN.
func gRwCopyVsRUnlock() int {
	var r gRwBox
	done := make(chan int)
	r.rw.RLock()
	go func() {
		r.rw.RUnlock()
		done <- 0
	}()
	gRwSink = r
	<-done
	return gRwSink.n
}

// G-2 copy (main) beside the write-Unlock ONLY (main Locks before the
// spawn; the child Unlocks). Same derivation -> over-refusal BY DESIGN.
func gRwCopyVsUnlock() int {
	var r gRwBox
	done := make(chan int)
	r.rw.Lock()
	go func() {
		r.rw.Unlock()
		done <- 0
	}()
	gRwSink = r
	<-done
	return gRwSink.n
}

// G-3 CONTROL: the canonical WaitGroup pattern — Add before the spawn, the
// child Dones, main Waits (the first and only waiter: its realized plain
// sema WRITE lands beside the child's Done, now an atomic write on the
// STATE word — a different word, no conflict) — then main COPIES the box
// AFTER Wait returned (HB-after the Done via Done's release / Wait's
// acquire). Expected: agree-DRF (a conflict here would mean the go_mem
// kinds collide with the realized sema pair).
func gWgCanonicalThenCopy() int {
	var w gWgBox
	w.wg.Add(1)
	go func() {
		w.n = 3
		w.wg.Done()
	}()
	w.wg.Wait()
	gWgSink = w
	return gWgSink.n
}

// G-4 CONTROL: a reader and a writer CONTEND on one RWMutex (the reader's
// RLock/RUnlock unordered with the writer's Lock/Unlock: read-like and
// write-like atomic kinds on the counter word beside plain reads of the
// `w` word — atomic/atomic never conflicts, the `w` reads are read/read),
// joined, then a copy AFTER the join. Expected: agree-DRF.
func gRwContendThenCopy() int {
	var r gRwBox
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
	gRwSink = r
	return gRwSink.n
}

// G-5 copy beside RLock ONLY: the child RLocks, then waits for main's ack
// before RUnlocking, so the copy is unordered with the LOCK op alone and
// HB-before the (write-like) RUnlock. go_mem: lock is read-like, the copy
// read-like -> NOT a race. TSan: read/read on rw.w -> GREEN. Expected:
// agree-DRF — the ruling's "NOT in the class" statement, isolated. (The
// u4kind subject `rw-copy-vs-rlock` pairs RLock with RUnlock unordered with
// the copy, so under the ruling it refuses THROUGH the RUnlock — it never
// isolated the lock op.)
func gRwCopyVsRLockOnly() int {
	var r gRwBox
	ack := make(chan int)
	done := make(chan int)
	go func() {
		r.rw.RLock()
		<-ack
		r.rw.RUnlock()
		done <- 0
	}()
	gRwSink = r
	ack <- 0
	<-done
	return gRwSink.n
}

// G-6 copy beside the write-Lock ONLY (same isolation) -> agree-DRF.
func gRwCopyVsLockOnly() int {
	var r gRwBox
	ack := make(chan int)
	done := make(chan int)
	go func() {
		r.rw.Lock()
		<-ack
		r.rw.Unlock()
		done <- 0
	}()
	gRwSink = r
	ack <- 0
	<-done
	return gRwSink.n
}

func main() {
	println(gRwCopyVsRUnlock(), gRwCopyVsUnlock(), gWgCanonicalThenCopy(), gRwContendThenCopy(),
		gRwCopyVsRLockOnly(), gRwCopyVsLockOnly())
}
