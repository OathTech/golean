package main

import "sync/atomic"

// MIXED ATOMIC/PLAIN MISUSE (atomics arc wave 1): a plain access to a
// word another goroutine operates on atomically, unordered by HB — a
// data race by mem#model (one write-like operand, one non-synchronizing)
// and mem#restrictions ("programs that ... modify data being
// simultaneously accessed by another goroutine"), reported by gc's
// -race build (TSan records the atomic op as an atomic access that
// conflicts with plain ones). RACY lane: every enumerated path must
// refuse; go run -race red (docs/evidence/2026-09-03_atomics-w1/probes).

// A plain WRITE beside a concurrent atomic Add on the same word.
func plainWriteVsAdd() int {
	var n int64
	done := make(chan struct{})
	go func() { atomic.AddInt64(&n, 1); done <- struct{}{} }()
	n = 5
	<-done
	return int(n)
}

// A plain READ beside a concurrent atomic Store on the same word.
func plainReadVsStore() int {
	var n int32
	done := make(chan struct{})
	go func() { atomic.StoreInt32(&n, 3); done <- struct{}{} }()
	r := n
	<-done
	return int(r)
}

// A plain read beside a concurrent CompareAndSwap — the CAS is an atomic
// WRITE whether it succeeds or fails (TSan records kAccessWrite on both
// paths; mem#model: a CAS is write-like).
func plainReadVsFailedCas() int {
	var n int32 = 1
	done := make(chan struct{})
	go func() { atomic.CompareAndSwapInt32(&n, 7, 8); done <- struct{}{} }() // fails: n is 1
	r := n
	<-done
	return int(r)
}

// A whole-struct COPY (a plain read of every field) beside a concurrent
// typed Add on the embedded atomic: the copy overlaps the `v` word.
type holder struct {
	tag  int
	hits atomic.Int64
}

func structCopyVsTypedAdd() int {
	h := &holder{tag: 1}
	done := make(chan struct{})
	go func() { h.hits.Add(1); done <- struct{}{} }()
	c := *h
	<-done
	return c.tag
}

// An atomic Swap beside a plain read of the same word.
func plainReadVsSwap() int {
	var n uint32 = 2
	done := make(chan struct{})
	go func() { atomic.SwapUint32(&n, 9); done <- struct{}{} }()
	r := n
	<-done
	return int(r)
}

func main() {
	plainWriteVsAdd()
	plainReadVsStore()
	plainReadVsFailedCas()
	structCopyVsTypedAdd()
	plainReadVsSwap()
}
