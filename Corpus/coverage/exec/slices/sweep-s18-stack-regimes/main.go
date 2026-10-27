package main

// S18 sweep — gc's members OUTSIDE slot 0 and the forms that fall back to growslice:
// the compiler's 32-byte stack buffer (a non-escaping result's first append from empty
// with a fixed element count and newLen ≤ 32/elemSize), gc 1.26's growsliceBuf ladder
// (cmd/compile/internal/slice) and its moveSliceNoCap escape, versus the spread and
// append-of-make forms that take the heap path even when non-escaping. Every gc draw is
// a member of the envelope [newLen, max(32, 2·growth)]; -race switches the optimisations
// off and lands on slot 0. Probe-verified go1.26.5, 2026-10-27.
var sinkInts []int

type St struct{ s []int }

//go:noinline
func str5() string { return "hello" }

//go:noinline
func buildInts3() []int {
	var s []int
	for i := 0; i < 3; i++ {
		s = append(s, i)
	}
	return s
}

// gc plain 16 (the stack buffer K = 16), -race 4 (slot 0)
func int16Nil1() int {
	var s []int16
	s = append(s, 1)
	return cap(s)
}

// gc 8 on both builds: the spread form has no stack buffer
func strSpreadNil() int {
	var b []byte
	b = append(b, str5()...)
	return cap(b)
}

// gc plain 3 (the ladder), -race 4 (slot 0)
func ladderInt3() int {
	var s []int
	for i := 0; i < 3; i++ {
		s = append(s, i)
	}
	c := cap(s)
	sinkInts = s
	return c
}

// gc plain 3 (moveSliceNoCap at the escape), -race 4 (slot 0)
func ladderRetInt3() int {
	return cap(buildInts3())
}

// gc 6 on both builds (extendSlice → growslice)
func makeSpreadNil() int {
	var s []int
	s = append(s, make([]int, 5)...)
	return cap(s)
}
