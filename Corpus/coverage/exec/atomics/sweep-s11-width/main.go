package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group R2: the sync/atomic integer kinds
// wrap at their own widths (the typed Int32/Int64/Uint32/Uint64/Uintptr methods and the function
// forms): an Add at the maximum, a decrement from zero by the two's-complement idiom, a Swap and a
// CompareAndSwap at the extremes. Single goroutine, strict.

import "sync/atomic"

func atomicTypedWraps() (int32, int64, uint32, uint64, uint64) {
	var a atomic.Int32
	a.Store(1<<31 - 1)
	a.Add(1)
	var b atomic.Int64
	b.Store(-1 << 63)
	b.Add(-1)
	var c atomic.Uint32
	c.Store(0)
	c.Add(^uint32(0))
	var d atomic.Uint64
	d.Store(1<<64 - 1)
	d.Add(1)
	var e atomic.Uintptr
	e.Store(0)
	e.Add(^uintptr(0))
	return a.Load(), b.Load(), c.Load(), d.Load(), uint64(e.Load())
}

func atomicFuncWraps() (int32, uint64, int64, bool, int32, uint32) {
	var x int32 = 1<<31 - 1
	atomic.AddInt32(&x, 1)
	var u uint64
	atomic.AddUint64(&u, ^uint64(0))
	var y int64 = -1 << 63
	r := atomic.AddInt64(&y, -1)
	ok := atomic.CompareAndSwapInt32(&x, -1<<31, 5)
	var w uint32 = 1<<32 - 1
	old := atomic.SwapUint32(&w, 0)
	return x, u, r, ok, atomic.LoadInt32(&x), old
}

func atomicAddReturns() (int8, int64, uint64) {
	var a atomic.Int32
	a.Store(127)
	v := a.Add(1)
	var b atomic.Int64
	b.Store(9223372036854775807)
	w := b.Add(1)
	var c atomic.Uint64
	c.Store(1)
	z := c.Add(^uint64(0))
	return int8(v), w, z
}

func main() {
	atomicTypedWraps()
	atomicFuncWraps()
	atomicAddReturns()
}
