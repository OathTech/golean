package main

import "sync/atomic"

// FRONTIER SUITE (slice 6, the whole-language bar): sync/atomic — the
// concurrency-entangled frontier row's cases-in-hand. mem#atomic is
// the normative text: "The APIs in the sync/atomic package are
// collectively 'atomic operations' … behave as if executed in some
// sequentially consistent order" (the sync-atomic clause; latitude
// inventory U-6 records the SC pin verbatim). All rows are RED at
// frontend-export by design until an atomics arc lands — the design
// question (what choice site realizes SC-over-atomics beside the L1
// scheduler envelope) is the row's owner, not a queue slot.
//
// Enumeration judgment (logged): the CORE OP CLASSES are enumerated —
// load, store, add, swap, compare-and-swap, and atomic.Value — on one
// or two integer widths each. The remaining typed variants
// (Uint*/Bool/Pointer[T]/Int32-vs-64 duplicates) ride the same
// lowering surface and are deliberately not duplicated row-for-row;
// the mp-litmus row is the one that pins the MODEL (SC excludes
// fs=1 ∧ ds=0), and it is the case the design memo consumes.

func atomicAddLoadStore() int {
	var n int64
	atomic.StoreInt64(&n, 5)
	atomic.AddInt64(&n, 3)
	var m int32
	atomic.AddInt32(&m, 2)
	return int(atomic.LoadInt64(&n))*10 + int(atomic.LoadInt32(&m)) // 82
}

func atomicCas() int {
	var n int32 = 4
	ok1 := atomic.CompareAndSwapInt32(&n, 4, 9) // succeeds
	ok2 := atomic.CompareAndSwapInt32(&n, 4, 7) // fails: n is 9
	v := 0
	if ok1 {
		v += 100
	}
	if ok2 {
		v += 10
	}
	return v + int(atomic.LoadInt32(&n)) // 109
}

func atomicSwap() int {
	var n int32 = 6
	old := atomic.SwapInt32(&n, 2)
	return int(old)*10 + int(atomic.LoadInt32(&n)) // 62
}

func atomicValue() int {
	var v atomic.Value
	v.Store(41)
	got := v.Load().(int)
	return got + 1 // 42
}

// The message-passing litmus: writer stores data THEN flag; reader
// (main) loads flag THEN data. mem#atomic's seq_cst sentence forbids
// exactly one outcome — flag seen written but data not (10). Admitted:
// 0 (reader first), 1 (reader between the stores… sees data only),
// 11 (reader last). gc sample at the pin: 400/400 → 0
// (artifacts/probe/slice6b/mp — one member witnessed; the set is
// argued from the mem text, which is the membership lane's job).
func atomicMpLitmus() int {
	var data, flag int32
	go func() {
		atomic.StoreInt32(&data, 1)
		atomic.StoreInt32(&flag, 1)
	}()
	fs := atomic.LoadInt32(&flag)
	ds := atomic.LoadInt32(&data)
	return int(fs)*10 + int(ds)
}

func main() {
	atomicAddLoadStore()
	atomicCas()
	atomicSwap()
	atomicValue()
	atomicMpLitmus()
}
