package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group R1 (BUG-055's site): gc keeps the
// WaitGroup counter in the high int32 of a uint64 state word (sync/waitgroup.go @ go1.26.5:
// `wg.state.Add(uint64(delta) << 32)`, `v := int32(state >> 32)`), so a delta wraps mod 2^32
// BEFORE the negative test: every boundary of that width — the maximum then one more (a panic),
// 1<<32 (the high word is 0: a no-op), 1<<32 + 1 (acts as 1), -(1<<31) (a panic), the maximum
// cancelled exactly, Done at zero, MinInt64 (a no-op), -(1<<31) - 1 (wraps to the maximum: no panic).

import "sync"

func wgAddMaxThenOne() int {
	var wg sync.WaitGroup
	wg.Add(1<<31 - 1)
	wg.Add(1)
	return 0
}

func wgAddTwoPow32() int {
	var wg sync.WaitGroup
	wg.Add(1 << 32)
	wg.Wait()
	return 1
}

func wgAddTwoPow32PlusOne() int {
	var wg sync.WaitGroup
	wg.Add(1<<32 + 1)
	wg.Done()
	wg.Wait()
	return 2
}

func wgAddNegTwoPow31() int {
	var wg sync.WaitGroup
	wg.Add(-(1 << 31))
	return 0
}

func wgAddMaxCancelled() int {
	var wg sync.WaitGroup
	wg.Add(1<<31 - 1)
	wg.Add(-(1<<31 - 1))
	wg.Wait()
	return 3
}

func wgDoneAtZero() int {
	var wg sync.WaitGroup
	wg.Done()
	return 0
}

func wgAddMinInt64() int {
	var wg sync.WaitGroup
	wg.Add(-9223372036854775808)
	wg.Wait()
	return 4
}

func wgAddBelowNegTwoPow31() int {
	var wg sync.WaitGroup
	wg.Add(-(1<<31) - 1)
	wg.Add(-(1<<31 - 1))
	wg.Wait()
	return 5
}

func main() {
	wgAddTwoPow32()
	wgAddTwoPow32PlusOne()
	wgAddMaxCancelled()
	wgAddMinInt64()
	wgAddBelowNegTwoPow31()
}
