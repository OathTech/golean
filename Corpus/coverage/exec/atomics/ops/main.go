package main

import "sync/atomic"

// sync/atomic INTEGER CORE — the direct-call op family, one subject per
// (op × kind) cell plus the shape rows (the atomics arc, wave 1;
// design note docs/2026-09-03_atomics-w1-design.md). Every subject is
// single-goroutine: these rows pin the VALUE semantics of each op
// (mem#atomic's SC clause is vacuous with one goroutine — the
// concurrency rows live in atomics/counter, race/atomics-free,
// race/atomics-misuse and sync/atomic-frontier/mp-litmus). Wrap
// arithmetic is spec#Integer_overflow's two's-complement wrap, which
// gc's Add realizes (AddUint32(&x, ^uint32(c-1)) is the documented
// decrement idiom).

func loadStoreInt32() int {
	var n int32 = 7
	atomic.StoreInt32(&n, -5)
	return int(atomic.LoadInt32(&n)) // -5
}

func loadStoreInt64() int {
	var n int64
	atomic.StoreInt64(&n, 1<<40)
	return int(atomic.LoadInt64(&n) >> 30) // 1024
}

func loadStoreUint32() int {
	var n uint32
	atomic.StoreUint32(&n, 0xFFFFFFFF)
	return int(atomic.LoadUint32(&n) >> 28) // 15
}

func loadStoreUint64() int {
	var n uint64
	atomic.StoreUint64(&n, 1<<63)
	return int(atomic.LoadUint64(&n) >> 60) // 8
}

func loadStoreUintptr() int {
	var n uintptr
	atomic.StoreUintptr(&n, 4096)
	return int(atomic.LoadUintptr(&n)) // 4096
}

func addInt32Wrap() int {
	var n int32 = 2147483647 // MaxInt32
	got := atomic.AddInt32(&n, 1)      // wraps to MinInt32
	if got != -2147483648 {
		return 1
	}
	return int(atomic.AddInt32(&n, -3)) + 2147483648 // MinInt32-3 wraps: 2147483645 -> +2^31 = 4294967293
}

func addInt64() int {
	var n int64 = 40
	a := atomic.AddInt64(&n, 5)
	b := atomic.AddInt64(&n, -3)
	return int(a)*100 + int(b) // 4542
}

func addUint32Decrement() int {
	var n uint32 = 3
	atomic.AddUint32(&n, ^uint32(0)) // the documented decrement idiom: 2
	atomic.AddUint32(&n, ^uint32(1)) // subtract 2: 0
	return int(atomic.AddUint32(&n, ^uint32(0))) // wraps to MaxUint32 = 4294967295
}

func addUint64() int {
	var n uint64 = 1<<63 - 1
	got := atomic.AddUint64(&n, 2) // 1<<63 + 1
	return int(got >> 62) // 2
}

func swapInt32() int {
	var n int32 = 6
	old := atomic.SwapInt32(&n, -2)
	return int(old)*10 + int(atomic.LoadInt32(&n)) // 60 + -2 = 58
}

func swapUint64() int {
	var n uint64 = 9
	old := atomic.SwapUint64(&n, 1<<40)
	return int(old)*10 + int(atomic.LoadUint64(&n)>>39) // 90 + 2 = 92
}

func casInt64() int {
	var n int64 = 4
	ok1 := atomic.CompareAndSwapInt64(&n, 4, 9) // succeeds
	ok2 := atomic.CompareAndSwapInt64(&n, 4, 7) // fails: n is 9
	v := 0
	if ok1 {
		v += 100
	}
	if ok2 {
		v += 10
	}
	return v + int(atomic.LoadInt64(&n)) // 109
}

func addUintptr() int {
	var n uintptr = 4096
	got := atomic.AddUintptr(&n, 16)
	return int(got) + int(atomic.AddUintptr(&n, ^uintptr(15))) // 4112 + 4096 = 8208
}

func swapUintptr() int {
	var n uintptr = 8
	old := atomic.SwapUintptr(&n, 1<<20)
	return int(old)*10 + int(atomic.LoadUintptr(&n)>>19) // 80 + 2 = 82
}

func swapInt64() int {
	var n int64 = -3
	old := atomic.SwapInt64(&n, 1<<40)
	return int(old)*10 + int(atomic.LoadInt64(&n)>>39) // -30 + 2 = -28
}

func swapUint32() int {
	var n uint32 = 1
	old := atomic.SwapUint32(&n, 0xFFFFFFFF)
	return int(old)*100 + int(atomic.LoadUint32(&n)>>28) // 100 + 15 = 115
}

func casUint64() int {
	var n uint64 = 1 << 63
	ok1 := atomic.CompareAndSwapUint64(&n, 1<<63, 3) // succeeds
	ok2 := atomic.CompareAndSwapUint64(&n, 1<<63, 4) // fails: n is 3
	v := 0
	if ok1 {
		v += 100
	}
	if ok2 {
		v += 10
	}
	return v + int(atomic.LoadUint64(&n)) // 103
}

func casUintptr() int {
	var n uintptr = 7
	if !atomic.CompareAndSwapUintptr(&n, 7, 9) {
		return -1
	}
	if atomic.CompareAndSwapUintptr(&n, 7, 11) {
		return -2
	}
	return int(atomic.LoadUintptr(&n)) // 9
}

func casUint32Fail() int {
	var n uint32 = 1
	if atomic.CompareAndSwapUint32(&n, 2, 3) {
		return -1
	}
	return int(atomic.LoadUint32(&n)) // 1 (untouched)
}

// Result DISCARDED (an expression statement): the op still lands.
func discardedResult() int {
	var n int64 = 10
	atomic.AddInt64(&n, 5)
	atomic.SwapInt64(&n, atomic.LoadInt64(&n)*2)
	atomic.CompareAndSwapInt64(&n, 30, 31)
	return int(n) // 31 — the plain read is same-goroutine, race-free
}

// In EXPRESSION position: the ANF hoist statement-anchors the op; the
// surrounding arithmetic sees the returned value.
func inExpression() int {
	var n int32 = 3
	x := atomic.AddInt32(&n, 4)*10 + int32(atomic.LoadInt32(&n))
	return int(x) // 77
}

// Operand EVALUATION ORDER (spec#Order_of_evaluation): address, then
// the value operands left to right; a side effect in each is observed
// in that order.
func operandOrder() int {
	var n int64 = 100
	trace := 0
	addr := func() *int64 { trace = trace*10 + 1; return &n }
	old := func() int64 { trace = trace*10 + 2; return 100 }
	nw := func() int64 { trace = trace*10 + 3; return 7 }
	if !atomic.CompareAndSwapInt64(addr(), old(), nw()) {
		return -1
	}
	return trace*10 + int(atomic.LoadInt64(&n)) // 1237
}

// A `type T int64` cell reached through a pointer conversion: the cell
// carries the underlying kind, so the op is defined on it.
type ticks int64

func definedUnderlying() int {
	var t ticks = 5
	atomic.AddInt64((*int64)(&t), 6)
	return int(t) // 11
}

// gc: the intrinsic faults on the nil address BEFORE any effect — a
// recoverable runtime error.
func nilAddress() int {
	var p *int64
	return int(atomic.AddInt64(p, 1))
}

func nilAddressRecovered() int {
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 1
			}
		}()
		var p *int32
		atomic.StoreInt32(p, 1)
	}()
	return r // 1
}

func main() {
	loadStoreInt32()
	loadStoreInt64()
	loadStoreUint32()
	loadStoreUint64()
	loadStoreUintptr()
	addInt32Wrap()
	addInt64()
	addUint32Decrement()
	addUint64()
	swapInt32()
	swapUint64()
	casInt64()
	addUintptr()
	swapUintptr()
	swapInt64()
	swapUint32()
	casUint64()
	casUintptr()
	casUint32Fail()
	discardedResult()
	inExpression()
	operandOrder()
	definedUnderlying()
	nilAddressRecovered()
}
