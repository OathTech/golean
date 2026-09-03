package main

// strings.Builder.Cap() through the REAL grow body with the :67 overlay
// (`bytealg.MakeNoZero(2*cap+n)` -> `append([]byte(nil), make([]byte,
// 2*cap+n)...)`, stdlib source-through slice 2, 2026-09-03). MakeNoZero's
// documented contract is "capacity of AT LEAST n" (gc realizes runtime
// size-class rounding: Grow(10) on an empty Builder -> 16, Grow(100) ->
// 112, "hello"+Grow(20) -> 48 at go1.26.5, probe-verified); the substitute
// realizes the language's own append-spill latitude, the machine's R2
// envelope [newLen, max(32, 2*growth)] (latitude inventory R2), which
// contains gc's point for every n. MEMBERSHIP rows: every `go run` sample
// must lie in the machine-enumerated set. Under the retired shadow model
// Cap was a declaration-only stub (a refusal); it is a real observable now.

import "strings"

// One spill: append([]byte(nil), make([]byte, 10)...) — envelope [10, 32]
// (oldCap 0, newLen 10: growth max(4,10)=10, upper max(32,20)=32); 23
// members. gc: 16.
func builderCapGrowEmpty() int {
	var b strings.Builder
	b.Grow(10)
	return b.Cap()
}

// One spill at newLen 100: envelope [100, 200]; 101 members. gc: 112.
func builderCapGrowHundred() int {
	var b strings.Builder
	b.Grow(100)
	return b.Cap()
}

// WriteString("hello") appends onto nil (cap c1 in [5, 32]); Grow(20)
// either already fits (c1 >= 25: Cap = c1) or grows to n = 2*c1+20 in
// [30, 68] with cap in [n, 2n] — the union is [25, 136]; 112 members.
// gc: c1 = 8, n = 36, cap 48.
func builderCapGrowAfterWrite() int {
	var b strings.Builder
	b.WriteString("hello")
	b.Grow(20)
	return b.Cap()
}

// Grow then an in-place write: the capacity is the ONE spill's choice
// ([10, 32], 23 members) and Len is exact — both observed. gc: 16, 3.
func builderCapGrowThenWrite() (int, int) {
	var b strings.Builder
	b.Grow(10)
	b.WriteString("abc")
	return b.Cap(), b.Len()
}

func main() {
	println(builderCapGrowEmpty())
	println(builderCapGrowHundred())
	println(builderCapGrowAfterWrite())
	c, l := builderCapGrowThenWrite()
	println(c, l)
}
