// TSan-realization probes for the sync/atomic detector edges (atomics
// arc wave 1; Race.lean, section "sync/atomic — the per-address
// clocks"). Each subject exercises ONE claim of the derivation table;
// the header states the expected `go run -race` verdict and why, and
// whether the verdict is schedule-INDEPENDENT (every run) or
// schedule-DEPENDENT (a race exists on some schedules; the sampler's
// counts vary run to run — reported as ranges in the README). Run per
// subject: `go run -race . <subject>` (run-tsan.sh does N runs per
// subject at GOMAXPROCS 1 and 8 and records RACE/green/other counts).
package main

import (
	"fmt"
	"os"
	"sync"
	"sync/atomic"
	"time"
)

// contend: two goroutines Add one word, no other sync. EXPECT green,
// every run (atomic↔atomic never conflicts — TSan's kAccessAtomic
// exclusion).
func contend() {
	var n int64
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { atomic.AddInt64(&n, 1); wg.Done() }()
	go func() { atomic.AddInt64(&n, 1); wg.Done() }()
	wg.Wait()
	fmt.Println(atomic.LoadInt64(&n))
}

// plainWriteVsAdd: a plain write beside an atomic Add. EXPECT RACE,
// every run (atomic write vs plain write, unordered on every schedule).
// Corpus twin: race/atomics-misuse/plain-write-vs-add.
func plainWriteVsAdd() {
	var n int64
	done := make(chan struct{})
	go func() { atomic.AddInt64(&n, 1); done <- struct{}{} }()
	n = 5
	<-done
	fmt.Println(n)
}

// plainReadVsStore: a plain read beside an atomic Store. EXPECT RACE,
// every run. Corpus twin: race/atomics-misuse/plain-read-vs-store.
func plainReadVsStore() {
	var n int32
	done := make(chan struct{})
	go func() { atomic.StoreInt32(&n, 3); done <- struct{}{} }()
	r := n
	<-done
	fmt.Println(r)
}

// plainReadVsSwap: a plain read beside an atomic Swap. EXPECT RACE,
// every run. Corpus twin: race/atomics-misuse/plain-read-vs-swap.
func plainReadVsSwap() {
	var n uint32 = 2
	done := make(chan struct{})
	go func() { atomic.SwapUint32(&n, 9); done <- struct{}{} }()
	r := n
	<-done
	fmt.Println(r)
}

// plainReadVsLoad: a plain read beside an atomic Load, nothing writes.
// EXPECT green, every run (read/read). Corpus twin:
// race/atomics-free/plain-read-vs-load.
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
// WRITE. EXPECT RACE, every run. Corpus twin:
// race/atomics-misuse/plain-read-vs-failed-cas.
func plainReadVsFailedCas() {
	var n int32 = 1
	done := make(chan struct{})
	go func() { atomic.CompareAndSwapInt32(&n, 7, 8); done <- struct{}{} }()
	r := n
	<-done
	fmt.Println(r)
}

// publish: writer stores data then flag; reader spins on the flag then
// reads data. EXPECT green, every run (store-release / load-acquire
// publishes). Corpus twin (non-spin, membership):
// race/atomics-free/publish-acquire.
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

// casSpinPublish: the reader spins on CompareAndSwap(&flag, 1, 1),
// which SUCCEEDS exactly when flag==1 — an RMW acquire on success; the
// failing iterations (flag still 0) acquire an EMPTY clock, so this
// subject exercises the SUCCESS acquire, not the failure one (its first
// header wrongly said the failure acquire could not be isolated — see
// casFailureAcquireIsolated, the auditor's shape). EXPECT green, every
// run.
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

// casFailureAcquireIsolated: THE FAILURE ACQUIRE, isolated (audit fix
// H5): the reader spins on CompareAndSwap(&flag, 0, 0), which SUCCEEDS
// while flag==0 and FAILS exactly on observing the store — the loop's
// exit is the FAILING CAS, and its acquire (TSan mo_acquire on failure;
// mem#atomic: the failed CAS observed the store) is the only edge
// ordering the plain data read after the plain write. EXPECT green,
// every run. Corpus twin: race/atomics-free/cas-failure-acquires.
func casFailureAcquireIsolated() {
	var data int64
	var flag int32
	go func() {
		data = 5
		atomic.StoreInt32(&flag, 1)
	}()
	for atomic.CompareAndSwapInt32(&flag, 0, 0) {
	}
	fmt.Println(data)
}

// rmwPublish: the reader spins on Add(&flag, 0) — an RMW acquires.
// EXPECT green, every run. Corpus twin: race/atomics-free/rmw-acquire.
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

// siblingWords: an atomic Add on `a` beside a plain read of the sibling
// variable `b`, joined by a WaitGroup. EXPECT green, every run (disjoint
// words). Corpus twin: race/atomics-free/sibling-words.
func siblingWords() {
	var a int64
	var b int64 = 3
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { atomic.AddInt64(&a, 4); wg.Done() }()
	r := b
	wg.Wait()
	fmt.Println(r + atomic.LoadInt64(&a))
}

// storeOverwrite: TWO writers each publish their own datum then store
// the SAME flag (A stores 1, B stores 2); the reader spins until the
// flag reads 2, then reads A's datum. SCHEDULE-DEPENDENT BY
// CONSTRUCTION: (i) A-store-then-B-store — B's ReleaseStore OVERWRITES
// the flag's clock (drops A's), so the reader's read of dataA is
// unordered with A's plain write → RACE; a merge model would call it
// green — THE DISCRIMINATOR; (ii) B-store-then-A-store — the flag is 1
// forever and the reader never exits: a TIMEOUT ("other"), by
// construction, not (only) starvation; (iii) A-store-then-B-store AND
// the reader's spin CATCHES the intermediate 1 — that load acquires
// A's clock directly, so the later read of dataA is ordered and the run
// is GREEN. So a green run is evidence of (iii), NOT of a merge model
// (a merge would make EVERY completed run green; the RACE cell's mere
// presence is the discriminator). Counts vary run to run; the README
// reports ranges.
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
// B spins on Add(&x, 0) until it observes 2. SCHEDULE-DEPENDENT and
// RACY BY go_mem on the executions where a spin RMW lands BETWEEN A's
// plain write and its store (an atomic RMW beside an unordered plain
// write) — so it does NOT isolate TSan's record-then-acquire order;
// the isolating shapes are plainThenStoreVsLate* below. Kept as the
// spin twin of plainThenStoreVsLoad; counts vary run to run.
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

// plainThenStoreVsLoad (SPIN form): the LOAD twin — SCHEDULE-DEPENDENT,
// racy by go_mem for the same reason (a spin LOAD between A's plain
// write and its store is an atomic read beside an unordered plain
// write: read-write race, one non-synchronizing). The first version of
// this header predicted green; the measurement corrected it.
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

// The isolating shapes for TSan's record-then-acquire order (design
// note §4; Race.lean's sync/atomic section): A: plain write x; atomic
// Store x. B: sleeps (real time only — no HB), then ONE atomic op on
// x. On the executions where B's op lands after the store (the sleep
// makes this overwhelmingly likely; a run where it lands before would
// be a real go_mem race and needs inspection, not dismissal), go_mem
// orders A's plain write before B's op (the store is synchronized
// before the op that observes it) — DRF; TSan records the op's atomic
// WRITE before acquiring the address clock and reports a race with A's
// plain write. EXPECT RACE for the RMW/CAS forms (the one recorded
// over-refusal vs literal go_mem — the machine refuses these schedules
// too), green for the Load form (acquire THEN record).

func lateWriter() (*int64, chan struct{}) {
	x := new(int64)
	done := make(chan struct{})
	go func() {
		*x = 1
		atomic.StoreInt64(x, 2)
		done <- struct{}{}
	}()
	time.Sleep(20 * time.Millisecond)
	return x, done
}

func plainThenStoreVsLateAdd() {
	x, done := lateWriter()
	v := atomic.AddInt64(x, 0)
	<-done
	fmt.Println(v)
}

func plainThenStoreVsLateSwap() {
	x, done := lateWriter()
	v := atomic.SwapInt64(x, 2)
	<-done
	fmt.Println(v)
}

// The CAS that SUCCEEDS (expected 2 = the stored value).
func plainThenStoreVsLateCasSuccess() {
	x, done := lateWriter()
	v := atomic.CompareAndSwapInt64(x, 2, 3)
	<-done
	fmt.Println(v)
}

// The CAS that FAILS (expected 7, never the value): still an atomic
// WRITE record before the (failure) acquire. EXPECT RACE.
func plainThenStoreVsLateCasFail() {
	x, done := lateWriter()
	v := atomic.CompareAndSwapInt64(x, 7, 8)
	<-done
	fmt.Println(v)
}

func plainThenStoreVsLateLoad() {
	x, done := lateWriter()
	v := atomic.LoadInt64(x)
	<-done
	fmt.Println(v)
}

// nilAddress: gc's -race build faults on the nil address BEFORE any
// TSan call — EXPECT the ordinary nil-dereference panic, no race
// report, every run.
func nilAddress() {
	defer func() { fmt.Println("recovered:", recover() != nil) }()
	var p *int64
	atomic.AddInt64(p, 1)
}

// structCopyVsTypedAdd: a whole-struct copy beside a typed Add on the
// embedded atomic.Int64. EXPECT RACE, every run (the copy reads the
// word). Corpus twin: race/atomics-misuse/struct-copy-vs-typed-add.
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
// EXPECT green, every run. Corpus twin:
// race/atomics-free/typed-sibling-field.
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
		"contend":                        contend,
		"plainWriteVsAdd":                plainWriteVsAdd,
		"plainReadVsStore":               plainReadVsStore,
		"plainReadVsSwap":                plainReadVsSwap,
		"plainReadVsLoad":                plainReadVsLoad,
		"plainReadVsFailedCas":           plainReadVsFailedCas,
		"publish":                        publish,
		"casSpinPublish":                 casSpinPublish,
		"casFailureAcquireIsolated":      casFailureAcquireIsolated,
		"rmwPublish":                     rmwPublish,
		"siblingWords":                   siblingWords,
		"storeOverwrite":                 storeOverwrite,
		"plainThenStoreVsAdd":            plainThenStoreVsAdd,
		"plainThenStoreVsLoad":           plainThenStoreVsLoad,
		"plainThenStoreVsLateAdd":        plainThenStoreVsLateAdd,
		"plainThenStoreVsLateSwap":       plainThenStoreVsLateSwap,
		"plainThenStoreVsLateCasSuccess": plainThenStoreVsLateCasSuccess,
		"plainThenStoreVsLateCasFail":    plainThenStoreVsLateCasFail,
		"plainThenStoreVsLateLoad":       plainThenStoreVsLateLoad,
		"nilAddress":                     nilAddress,
		"structCopyVsTypedAdd":           structCopyVsTypedAdd,
		"typedSiblingField":              typedSiblingField,
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
