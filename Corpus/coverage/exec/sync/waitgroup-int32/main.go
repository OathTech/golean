package main

import "sync"

// ARC-END fix-round pins (2026-08-10): the WaitGroup counter is an
// int32 in gc — the high 32 bits of a uint64 state word
// (waitgroup.go:104 `wg.state.Add(uint64(delta) << 32)`, :109
// `v := int32(state >> 32)`) — so the counter arithmetic wraps mod
// 2^32 BEFORE the `v < 0` panic test. The model's unbounded-Int
// counter diverged in BOTH directions (verifier-reproduced):
// a missed panic past 2^31-1 and a fabricated panic on a delta whose
// low 32 bits are zero. Red-first before the wrap fix.

// gc: uint32(1<<31) lands the high word at bit pattern 2^31 →
// int32 reads -2^31 → panic "sync: negative WaitGroup counter".
// The unbounded model proceeded silently with counter 2^31.
func addOverflowPanics() int {
	var wg sync.WaitGroup
	wg.Add(1 << 31)
	return 0
}

// gc: uint64(-(1<<32)) << 32 == 0 — the state word is UNCHANGED, the
// counter stays 0, no panic, returns 7. The unbounded model computed
// counter -2^32 < 0 and fabricated the panic.
func addWrapNoop() int {
	var wg sync.WaitGroup
	wg.Add(-(1 << 32))
	return 7
}

func main() {
	addWrapNoop()
}
