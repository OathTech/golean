package main

import (
	"sync"
	"sync/atomic"
)

// CONCURRENT COUNTER IDIOMS (atomics arc wave 1): two goroutines Add,
// WaitGroup.Wait, Load — the observation is schedule-INDEPENDENT (the
// Adds commute, the Done→Wait edge orders the final Load), so these are
// CONFLUENT rows: every enumerated schedule must yield the one value,
// and every schedule must be race-free (the atomics never conflict
// with each other; the final plain-vs-atomic mix is ordered by Wait).
// SC per mem#atomic is what makes "no lost update" a theorem here: each
// Add is one indivisible step in the machine, one LOCK-prefixed
// instruction in gc.

// (Spawns are UNROLLED rather than looped — a spawn loop's back-edges
// are scheduling consults, stage D §5d — and TWO goroutines contend:
// three exceeded the dedup budget at 1.8M nodes even unrolled; the
// idiom's content is the concurrent Adds, not their count.)
func counterAdd() int {
	var n int64
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { atomic.AddInt64(&n, 2); wg.Done() }()
	go func() { atomic.AddInt64(&n, 3); wg.Done() }()
	wg.Wait()
	return int(atomic.LoadInt64(&n)) // 5
}

func counterTyped() int {
	var c atomic.Int32
	var wg sync.WaitGroup
	wg.Add(2)
	go func(d int32) { c.Add(d); wg.Done() }(1)
	go func(d int32) { c.Add(d); wg.Done() }(2)
	wg.Wait()
	return int(c.Load()) // 3
}

// A CAS retry loop against a concurrent Add: a failed CAS means the
// Add landed between the Load and the CAS, so the loop is bounded on
// EVERY schedule (no spin-wait: no nonterm branches) — both increments
// land exactly once. The retry loop's back-edges are explored
// exhaustively (backedge=full); the contender is a single Add so the
// tree stays gate-sized (two retry loops took ~100 s).
func casLoopIncrement() int {
	var n int32
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		for {
			old := atomic.LoadInt32(&n)
			if atomic.CompareAndSwapInt32(&n, old, old+1) {
				break
			}
		}
		wg.Done()
	}()
	go func() { atomic.AddInt32(&n, 1); wg.Done() }()
	wg.Wait()
	return int(atomic.LoadInt32(&n)) // 2
}

// Swap as a one-shot claim: exactly one goroutine sees the old value 0
// and claims; the others see nonzero. Confluent: the claimant count is
// 1 whichever goroutine wins.
func swapClaim() int {
	var flag int32
	var claims int32
	var wg sync.WaitGroup
	wg.Add(2)
	claim := func() {
		if atomic.SwapInt32(&flag, 1) == 0 {
			atomic.AddInt32(&claims, 1)
		}
		wg.Done()
	}
	go claim()
	go claim()
	wg.Wait()
	return int(atomic.LoadInt32(&claims))*10 + int(atomic.LoadInt32(&flag)) // 11
}

// Plain read AFTER the join: Wait's acquire orders the child's atomic
// writes before main's plain read of the same word — race-free, and the
// value is the SC-final one.
func plainReadAfterJoin() int {
	var n int64
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { atomic.AddInt64(&n, 10); wg.Done() }()
	go func() { atomic.AddInt64(&n, 20); wg.Done() }()
	wg.Wait()
	return int(n) // 30
}

func main() {
	counterAdd()
	counterTyped()
	casLoopIncrement()
	swapClaim()
	plainReadAfterJoin()
}
