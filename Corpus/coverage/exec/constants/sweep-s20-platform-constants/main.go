package main

// Defect-neighbourhood campaign, shape S20 (the admission boundary), lane
// sweep/s20-admission, 2026-10-27: a strict row (expected = gc go1.26.5 under the
// runners' pins) on a route no earlier row held; the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4.
// E1–E4: the platform constants gc folds for linux/amd64 — runtime.GOOS/GOARCH/
// Compiler, math.MaxInt/MaxUint/MinInt, strconv.IntSize, bits.UintSize, the
// int-size idioms, and wrap-around at the 64-bit width — agree with the pinned
// Platform (unsafe's layout operators are BUG-070's refusal, not here).

import (
	"math"
	"math/bits"
	"runtime"
	"strconv"
)

func runtimeTarget() string   { return runtime.GOOS + "/" + runtime.GOARCH }
func runtimeCompiler() string { return runtime.Compiler }

func intSizeConstants() int {
	r := 0
	if math.MaxInt == 1<<63-1 {
		r += 1
	}
	if math.MaxUint == 1<<64-1 {
		r += 2
	}
	if math.MinInt == -1<<63 {
		r += 4
	}
	return r*10000 + strconv.IntSize*100 + bits.UintSize
}

func maxIntValue() int   { return math.MaxInt }
func maxUintValue() uint { return math.MaxUint }

const intSize = 32 << (^uint(0) >> 63)

func intSizeIdioms() int {
	r := intSize
	if ^uintptr(0) == 1<<64-1 {
		r += 1000
	}
	var u uint = ^uint(0)
	if u>>63 == 1 {
		r += 100000
	}
	return r
}

func wrapAtWidth() int {
	x := 1 << 62
	x *= 2
	x *= 2
	return x
}
