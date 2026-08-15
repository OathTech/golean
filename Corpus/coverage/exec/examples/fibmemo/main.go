package main

import "fmt"

// fibmemo: recursive Fibonacci over a real, load-bearing memo table
// (`map[uint64]uint64`) — the gallery campaign's chartered consumer of
// the MapMem proof kit (G1, 2026-08-15). The memo is read with the
// comma-ok form: Go's `memo[k]` on an absent key yields the zero value
// 0, and fib(0) = 0, so a naive `if memo[n] != 0` cache check cannot
// tell "cached 0" from "absent". The explicit `n < 2` base-case guard
// plus `v, ok := memo[n]` makes the absent/present distinction honest.
//
// Fuel note: the machine is fuel-bounded, so every corpus row keeps
// n <= 30 (memoization makes the recursion linear in n, but the bound
// is stated and respected in cases.tsv regardless).
func fibMemo(n uint64, memo map[uint64]uint64) uint64 {
	if n < 2 {
		return n
	}
	if v, ok := memo[n]; ok {
		return v
	}
	r := fibMemo(n-1, memo) + fibMemo(n-2, memo)
	memo[n] = r
	return r
}

// fib: wrapper subject — allocates the memo table and runs the
// memoized recursion.
func fib(n uint64) uint64 {
	memo := make(map[uint64]uint64)
	return fibMemo(n, memo)
}

// fibMemoSize: map-observing driver — run the memoized computation,
// then count the memo's entries with `for range`. The observable
// depends on map iteration only through its COUNT, which is
// order-invariant (deliberate; mirrors the histogram flagship's
// distinct-count summary).
func fibMemoSize(n uint64) uint64 {
	memo := make(map[uint64]uint64)
	fibMemo(n, memo)
	size := uint64(0)
	for range memo {
		size++
	}
	return size
}

// fibmemo_harness: the harness ruling's three-phase shape, S2 scalar.
// setup: nothing — fib takes no memory input (the memo is internal).
// test: identity — the returned scalar IS the observable.
func fibmemo_harness(n uint64) uint64 {
	return fib(n)
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", fib(10))
}
