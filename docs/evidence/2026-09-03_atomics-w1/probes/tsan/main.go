// TSan-realization probes for the sync/atomic detector edges (atomics
// arc wave 1; Race.lean, section "sync/atomic — the per-address
// clocks"). Each subject exercises ONE claim of the derivation table;
// the header states the expected `go run -race` verdict and why. Run
// per subject: `go run -race . <subject>` (the runner script
// run-tsan.sh does N runs per subject at GOMAXPROCS 1 and 8 and
// records RACE/green counts).
package main

import (
	"fmt"
	"os"
	"sync"
	"sync/atomic"
	"time"
)

// contend: two goroutines Add one word, no other sync. EXPECT green
// (atomic↔atomic never conflicts — TSan's kAccessAtomic exclusion).
func contend() {
	var n int64
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { atomic.AddInt64(&n, 1); wg.Done() }()
	go func() { atomic.AddInt64(&n, 1); wg.Done() }()
	wg.Wait()
	fmt.Println(atomic.LoadInt64(&n))
}

// plainWriteVsAdd: a plain write beside an atomic Add. EXPECT RACE
// (atomic write vs plain write).
func plainWriteVsAdd() {
	var n int64
	done := make(chan struct{})
	go func() { atomic.AddInt64(&n, 1); done <- struct{}{} }()
	n = 5
	<-done
	fmt.Println(n)
}

// plainReadVsLoad: a plain read beside an atomic Load, nothing writes.
// EXPECT green (read/read).
func plainReadVsLoad() {
	var n int64 = 5
	done := make(chan struct{})
	var got int64
	go func() { got = atomic.LoadInt64(&n); done <- struct{}{} }()
	r := n
	<-done
	fmt.Println(r, got)
}

// plainReadVsFailedCas: a FAILED CAS is still recorded as an atomic
// WRITE. EXPECT RACE.
func plainReadVsFailedCas() {
	var n int32 = 1
	done := make(chan struct{})
	go func() { atomic.CompareAndSwapInt32(&n, 7, 8); done <- struct{}{} }()
	r := n
	<-done
	fmt.Println(r)
}

// publish: writer stores data then flag; reader spins on the flag then
// reads data. EXPECT green (store-release / load-acquire publishes).
func publish() {
	var data int64
	var flag int32
	go func() {
		data = 42
		atomic.StoreInt32(&flag, 1)
	}()
	for atomic.LoadInt32(&flag) == 0 {
	}
	fmt.Println(data)
}

// casFailAcquires: the reader's FAILED CAS (expected 5, flag is 0 or 1)
// followed by a spin-free conditional read: only if the failed CAS
// returned false AND a subsequent load sees 1... — to isolate the
// FAILURE acquire, the reader spins with a CAS that always fails:
// CAS(&flag, 5, 6) fails whether flag is 0 or 1; the loop exits when
// a LOAD-free probe... we cannot read the value from a failed Go CAS
// (Go returns only the bool), so the shape is: spin on
// CompareAndSwap(&flag, 1, 1) — which SUCCEEDS exactly when flag==1
// (an RMW acquire) — the failure-acquire is exercised by the
// iterations that fail while flag is still 0 (they acquire an empty
// clock — unobservable). Recorded honestly: Go's API cannot isolate
// the failure acquire with an observable effect; TSan's source is the
// citation. EXPECT green.
func casSpinPublish() {
	var data int64
	var flag int32
	go func() {
		data = 42
		atomic.StoreInt32(&flag, 1)
	}()
	for !atomic.CompareAndSwapInt32(&flag, 1, 1) {
	}
	fmt.Println(data)
}

// rmwPublish: the reader spins on Add(&flag, 0) — an RMW acquires.
// EXPECT green.
func rmwPublish() {
	var data int64
	var flag int32
	go func() {
		data = 42
		atomic.StoreInt32(&flag, 1)
	}()
	for atomic.AddInt32(&flag, 0) == 0 {
	}
	fmt.Println(data)
}

// storeOverwrite: TWO writers each publish their own datum then store
// the SAME flag; the reader spins until it sees writer B's value (2)
// and then reads writer A's datum. TSan's ReleaseStore OVERWRITES the
// flag's clock (B's store drops A's clock) — EXPECT RACE on the
// schedule A-store-then-B-store (A's plain write of dataA unordered
// with the reader's read); a merge model would call it green.
// Schedule-dependent: RACE in some runs is the discriminator.
func storeOverwrite() {
	var dataA, dataB int64
	var flag int32
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { dataA = 1; atomic.StoreInt32(&flag, 1); wg.Done() }()
	go func() { dataB = 2; atomic.StoreInt32(&flag, 2); wg.Done() }()
	for atomic.LoadInt32(&flag) != 2 {
	}
	fmt.Println(dataA + 0*dataB)
	wg.Wait()
}

// plainThenStoreVsAdd (SPIN form): A: plain write x; atomic Store x.
// B spins on Add(&x, 0) until it observes 2. MEASURED (first run):
// RACE 20/20 at GOMAXPROCS 8, 2/20 at 1. Read honestly, this shape is
// RACY BY go_mem on the executions where a spin RMW lands BETWEEN A's
// plain write and its store (an atomic RMW beside an unordered plain
// write) — so it does NOT isolate TSan's record-then-acquire order;
// the isolating shape is plainThenStoreVsLateAdd below. Kept as the
// spin twin of plainThenStoreVsLoad.
func plainThenStoreVsAdd() {
	var x int64
	go func() {
		x = 1
		atomic.StoreInt64(&x, 2)
	}()
	for atomic.AddInt64(&x, 0) != 2 {
	}
	fmt.Println(atomic.LoadInt64(&x))
}

// plainThenStoreVsLoad (SPIN form): the LOAD twin. MEASURED: RACE
// 20/20 at GOMAXPROCS 8, green 20/20 at 1 — racy by go_mem for the
// same reason as the Add twin (a spin LOAD landing between A's plain
// write and its store is an atomic read beside an unordered plain
// write: read-write race, one non-synchronizing). The first version of
// this header predicted green; the measurement corrected it. The
// isolating shape is plainThenStoreVsLateLoad below.
func plainThenStoreVsLoad() {
	var x int64
	go func() {
		x = 1
		atomic.StoreInt64(&x, 2)
	}()
	for atomic.LoadInt64(&x) != 2 {
	}
	fmt.Println(atomic.LoadInt64(&x))
}

// plainThenStoreVsLateAdd: THE ISOLATING SHAPE for TSan's
// record-then-acquire order on RMWs. A: plain write x; atomic Store x.
// B: sleeps (no HB — real time only), then ONE Add(&x, 0). On the
// executions where the Add lands after the store (the sleep makes
// this overwhelmingly likely), go_mem orders A's plain write before
// B's Add (the store is synchronized before the RMW that observes
// it) — DRF; TSan records B's atomic WRITE before acquiring the
// address clock and reports a race with A's plain write. EXPECT RACE
// (the one recorded over-refusal vs literal go_mem — Race.lean's
// sync/atomic section; the machine refuses these schedules too).
func plainThenStoreVsLateAdd() {
	var x int64
	done := make(chan struct{})
	go func() {
		x = 1
		atomic.StoreInt64(&x, 2)
		done <- struct{}{}
	}()
	time.Sleep(20 * time.Millisecond)
	v := atomic.AddInt64(&x, 0)
	<-done
	fmt.Println(v)
}

// plainThenStoreVsLateLoad: the LOAD twin of the isolating shape — the
// load acquires THEN records, so on the after-the-store executions A's
// plain write is ordered before the atomic read. EXPECT green (a run
// where the load lands before the store would be a real go_mem race;
// the sleep makes it vanishingly unlikely — a red here would need
// inspection, not dismissal).
func plainThenStoreVsLateLoad() {
	var x int64
	done := make(chan struct{})
	go func() {
		x = 1
		atomic.StoreInt64(&x, 2)
		done <- struct{}{}
	}()
	time.Sleep(20 * time.Millisecond)
	v := atomic.LoadInt64(&x)
	<-done
	fmt.Println(v)
}

// nilAddress: gc's -race build faults on the nil address BEFORE any
// TSan call — EXPECT the ordinary nil-dereference panic, no race
// report.
func nilAddress() {
	defer func() { fmt.Println("recovered:", recover() != nil) }()
	var p *int64
	atomic.AddInt64(p, 1)
}

// structCopyVsTypedAdd: a whole-struct copy beside a typed Add on the
// embedded atomic.Int64. EXPECT RACE (the copy reads the word).
type holder struct {
	tag  int
	hits atomic.Int64
}

func structCopyVsTypedAdd() {
	h := &holder{tag: 1}
	done := make(chan struct{})
	go func() { h.hits.Add(1); done <- struct{}{} }()
	c := *h
	<-done
	fmt.Println(c.tag)
}

// typedSiblingField: a plain read of a SIBLING field beside a typed Add.
// EXPECT green.
type stats struct {
	hits atomic.Int64
	name string
}

func typedSiblingField() {
	s := &stats{name: "s"}
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { s.hits.Add(2); wg.Done() }()
	n := len(s.name)
	wg.Wait()
	fmt.Println(n, s.hits.Load())
}

func main() {
	subjects := map[string]func(){
		"contend":                  contend,
		"plainWriteVsAdd":          plainWriteVsAdd,
		"plainReadVsLoad":          plainReadVsLoad,
		"plainReadVsFailedCas":     plainReadVsFailedCas,
		"publish":                  publish,
		"casSpinPublish":           casSpinPublish,
		"rmwPublish":               rmwPublish,
		"storeOverwrite":           storeOverwrite,
		"plainThenStoreVsAdd":      plainThenStoreVsAdd,
		"plainThenStoreVsLoad":     plainThenStoreVsLoad,
		"plainThenStoreVsLateAdd":  plainThenStoreVsLateAdd,
		"plainThenStoreVsLateLoad": plainThenStoreVsLateLoad,
		"nilAddress":               nilAddress,
		"structCopyVsTypedAdd":     structCopyVsTypedAdd,
		"typedSiblingField":        typedSiblingField,
	}
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: probe <subject>")
		os.Exit(2)
	}
	f, ok := subjects[os.Args[1]]
	if !ok {
		fmt.Fprintln(os.Stderr, "unknown subject", os.Args[1])
		os.Exit(2)
	}
	f()
}
