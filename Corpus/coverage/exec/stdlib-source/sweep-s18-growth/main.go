package main

// S18 sweep — capacity growth in the lowered stdlib (source-through): strings.Builder
// (WriteString's spread append; grow through the :67 overlay `append([]byte(nil),
// make([]byte, 2·cap+n)...)` for MakeNoZero's roundupsize), bytes.Buffer (the EXACT 64-byte
// small buffer for a first allocation ≤ 64, then growSlice's `append([]byte(nil),
// make([]byte, c)...)` with c = max(len+n, 2·cap)), and the slices package (Grow's
// append-of-make, Clone's spread, Concat, Insert, the exact Repeat/Clip). Strict where the
// size is exact or tape-invariant; membership with default=gc where gc's point is the
// runtime's growslice, which is the machine's slot 0. Probe-verified go1.26.5, 2026-10-27.
import "bytes"
import "slices"
import "strings"

//go:noinline
func str60() string {
	s := "a"
	for len(s) < 60 {
		s += s
	}
	return s[:60]
}

// gc 8 on both builds = slot 0
func builderWriteString() int {
	var b strings.Builder
	b.WriteString("hello")
	return b.Cap()
}

// Reset drops the buffer: Cap 0 at every capacity (strict)
func builderResetCap() int {
	var b strings.Builder
	b.WriteString("hello")
	b.Reset()
	return b.Cap()
}

// Grow(0) on an empty Builder allocates nothing: Cap 0
func builderGrow0() int {
	var b strings.Builder
	b.Grow(0)
	return b.Cap()
}

// Len is exact across two spills (tape-invariant: strict)
func builderLenAfterGrowth() int {
	var b strings.Builder
	b.WriteString("hello")
	b.WriteString("0123456789")
	return b.Len()
}

// bytes.Buffer.grow on an empty buffer with n ≤ 64: `make([]byte, n, smallBufferSize)` — EXACTLY 64, no latitude
func bufferGrow10() int {
	var b bytes.Buffer
	b.Grow(10)
	return b.Cap()
}

// the boundary n = 64 still takes the exact small buffer: 64
func bufferGrow64() int {
	var b bytes.Buffer
	b.Grow(64)
	return b.Cap()
}

// a first WriteString of 5 bytes goes through grow(5) → the exact 64-byte small buffer
func bufferWriteHello() int {
	var b bytes.Buffer
	b.WriteString("hello")
	return b.Cap()
}

// a first WriteByte: the exact 64-byte small buffer
func bufferWriteByte() int {
	var b bytes.Buffer
	b.WriteByte('a')
	return b.Cap()
}

// Reset keeps the backing: Cap stays 64
func bufferResetCap() int {
	var b bytes.Buffer
	b.WriteString("hello")
	b.Reset()
	return b.Cap()
}

// gc 128 = slot 0
func bufferWrite60Then10() int {
	var b bytes.Buffer
	b.WriteString(str60())
	b.WriteString("0123456789")
	return b.Cap()
}

// gc 60 (cap 6, len 0) = slot 0
func slicesGrowNil5() int {
	s := slices.Grow([]int(nil), 5)
	return cap(s)*10 + len(s)
}

// gc 6 = slot 0
func slicesClone5() int {
	s := slices.Clone([]int{1, 2, 3, 4, 5})
	return cap(s)
}

// Grow with room allocates nothing: cap unchanged (exact)
func slicesGrowRoom() int {
	s := make([]int, 2, 10)
	s = slices.Grow(s, 5)
	return cap(s)
}

// Clone preserves nil: nil, cap 0
func slicesCloneNil() int {
	s := slices.Clone([]int(nil))
	if s == nil {
		return 100 + cap(s)
	}
	return cap(s)
}

// slices.Repeat is a make of the exact product length: cap 6
func slicesRepeat() int {
	s := slices.Repeat([]int{1, 2}, 3)
	return cap(s)
}

// Clip is s[:len:len]: cap exactly len
func slicesClip() int {
	s := make([]int, 2, 10)
	s = slices.Clip(s)
	return cap(s)
}
