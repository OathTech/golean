package main

import "fmt"

func push(s []uint64, v uint64) []uint64 {
	return append(s, v)
}

func pop(s []uint64) ([]uint64, uint64) {
	v := s[len(s)-1]
	return s[:len(s)-1], v
}

func peek(s []uint64) uint64 {
	return s[len(s)-1]
}

func size(s []uint64) uint64 {
	return uint64(len(s))
}

// pushPopThree: push a, b, c then pop all three, returning the values
// in pop order — LIFO, so the result is (c, b, a).
func pushPopThree(a, b, c uint64) (uint64, uint64, uint64) {
	s := []uint64{}
	s = push(s, a)
	s = push(s, b)
	s = push(s, c)
	var x, y, z uint64
	s, x = pop(s)
	s, y = pop(s)
	_, z = pop(s)
	return x, y, z
}

func pushPeek(a, b uint64) uint64 {
	s := []uint64{}
	s = push(s, a)
	s = push(s, b)
	return peek(s)
}

func emptySize() uint64 {
	s := []uint64{}
	return size(s)
}

// stackCapN: the fixed observation cap of the S3 relational harness.
// Both returned arrays are `[stackCapN]uint64`, so the harness's own
// bound is `n <= 8` — plainly visible in the source.
const stackCapN = 8

// stack_harness_r: the S3 RELATIONAL harness. Setup pushes the family
// seed + i (wrapping) for i < n, recording each pushed value; the test
// pops min(k, n) values, recording them in pop order; the observable is
// (pushed, popped, remaining size). The Lean postcondition relates the
// returned data directly: popped is the suffix of pushed, reversed —
// popped[j] = pushed[n-1-j] for j < min(k, n) — and remaining =
// n - min(k, n). Real Go, ghost ladder rung 0.
func stack_harness_r(n, seed, k uint64) ([stackCapN]uint64, [stackCapN]uint64, uint64) {
	s := []uint64{}
	var pushed [stackCapN]uint64
	for i := uint64(0); i < n; i++ {
		v := seed + i
		s = push(s, v)
		pushed[i] = v
	}
	m := k
	if n < m {
		m = n
	}
	var popped [stackCapN]uint64
	for j := uint64(0); j < m; j++ {
		var v uint64
		s, v = pop(s)
		popped[j] = v
	}
	return pushed, popped, size(s)
}

func main() {
	x, y, z := pushPopThree(1, 2, 3)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		x, y, z,
	)
}
