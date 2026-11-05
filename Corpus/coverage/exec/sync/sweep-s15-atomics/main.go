package main

import "sync/atomic"

// Sweep S15 (scheduling boundaries and the menu), group A14/G3: the
// atomics as registry boundaries whose L1 order IS the sequentially
// consistent order mem#atomic pins (latitude inventory U-6). The MP
// litmus is sync/atomic-frontier/mp-litmus; these are its neighbours:
// store buffering (SC forbids 00), load buffering (SC forbids 11), the
// winner order of two Swaps and of two CompareAndSwaps, and the join of
// two Adds. The matrix is in docs/defect-shapes.md (S15).

// SB: each goroutine stores its own flag then loads the other's. SC
// forbids both loads returning 0.
func sbLitmus() int {
	var x, y int32
	var r1, r2 int32
	done := make(chan int, 2)
	go func() {
		atomic.StoreInt32(&x, 1)
		r1 = atomic.LoadInt32(&y)
		done <- 1
	}()
	go func() {
		atomic.StoreInt32(&y, 1)
		r2 = atomic.LoadInt32(&x)
		done <- 1
	}()
	<-done
	<-done
	return int(r1)*10 + int(r2)
}

// LB: each goroutine loads the other's flag then stores its own. SC
// forbids both loads returning 1.
func lbLitmus() int {
	var x, y int32
	var r1, r2 int32
	done := make(chan int, 2)
	go func() {
		r1 = atomic.LoadInt32(&y)
		atomic.StoreInt32(&x, 1)
		done <- 1
	}()
	go func() {
		r2 = atomic.LoadInt32(&x)
		atomic.StoreInt32(&y, 1)
		done <- 1
	}()
	<-done
	<-done
	return int(r1)*10 + int(r2)
}

// Two Swaps on one word: the second swapper sees the first one's value.
// a-first gives (a, b) = (0, 1) → 1; b-first gives (2, 0) → 20.
func swapOrder() int {
	var x int32
	var a, b int32
	done := make(chan int, 2)
	go func() {
		a = atomic.SwapInt32(&x, 1)
		done <- 1
	}()
	go func() {
		b = atomic.SwapInt32(&x, 2)
		done <- 1
	}()
	<-done
	<-done
	return int(a)*10 + int(b)
}

// Two CompareAndSwaps from 0: exactly one succeeds. 11 when a won,
// 102 when b won.
func casOrder() int {
	var x int32
	var a, b bool
	done := make(chan int, 2)
	go func() {
		a = atomic.CompareAndSwapInt32(&x, 0, 1)
		done <- 1
	}()
	go func() {
		b = atomic.CompareAndSwapInt32(&x, 0, 2)
		done <- 1
	}()
	<-done
	<-done
	r := int(atomic.LoadInt32(&x))
	if a {
		r += 10
	}
	if b {
		r += 100
	}
	return r
}

// Two Adds on one word, read after the join: 7 on every schedule.
func addJoin() int {
	var x int64
	done := make(chan int, 2)
	go func() {
		atomic.AddInt64(&x, 3)
		done <- 1
	}()
	go func() {
		atomic.AddInt64(&x, 4)
		done <- 1
	}()
	<-done
	<-done
	return int(atomic.LoadInt64(&x))
}

func main() {
	sbLitmus()
	lbLitmus()
	swapOrder()
	casOrder()
	addJoin()
}
