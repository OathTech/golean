package main

// The deterministic maxAlloc panic class (fidelity decision 5(b) [USER]
// 2026-08-31; latitude inventory R16; t5-maxalloc slice 2026-09-02). gc
// panics — recoverably, not an OOM abort — when ONE allocation request's
// byte size exceeds runtime.maxAlloc (1<<48 on linux/amd64): the slice
// check is `elemSize*n > 1<<48` (len blamed before cap, issue 4085), the
// channel check sits 112 bytes lower (`hchanSize`), the map hint is
// silently clamped (never a panic — and, BUG-082, not lowered by the
// native frontend at all until its 2026-09-02 fix), and a zero-size element never trips
// the limit. Every threshold below is JUST OVER: the just-under requests
// pass gc's check and then fail to ALLOCATE (fatal "out of memory"), the
// true-OOM class this corpus deliberately does not model (doctrine
// register #7 rider / discrepancy D-001).

// paddedElem is 16 bytes under gc's layout (9 bytes of fields + 7 of
// padding): the threshold 1<<44+1 is only a panic if padding is counted.
type paddedElem struct {
	a int64
	b byte
}

func makeMaxAllocSliceLenOverByte() {
	n := 1<<48 + 1
	_ = make([]byte, n)
}

func makeMaxAllocSliceLenOverConst() {
	_ = make([]byte, 1<<48+1)
}

func makeMaxAllocSliceLenOverInt64() {
	n := 1<<45 + 1
	_ = make([]int64, n)
}

func makeMaxAllocSliceLenOverPaddedStruct() {
	n := 1<<44 + 1
	_ = make([]paddedElem, n)
}

func makeMaxAllocSliceCapOverByte() {
	n := 1<<48 + 1
	_ = make([]byte, 0, n)
}

func makeMaxAllocSliceLenAndCapOver() {
	n := 1<<48 + 1
	_ = make([]byte, n+1, n)
}

func makeMaxAllocChanSizeOverByte() {
	n := 1 << 48
	_ = make(chan byte, n)
}

func makeMaxAllocChanSizeHeaderBoundary() {
	n := 1<<48 - 111
	_ = make(chan byte, n)
}

func makeMaxAllocChanSizeOverInt64() {
	n := 1 << 45
	_ = make(chan int64, n)
}

func makeMaxAllocChanZeroSizeElemHuge() int {
	n := 1 << 62
	c := make(chan struct{}, n)
	if cap(c) == n {
		return 1
	}
	return 0
}

func makeMaxAllocMapHintOver() int {
	n := 1<<48 + 1
	m := make(map[int]int, n)
	m[1] = 2
	return len(m)
}

func makeMaxAllocMapHintNegative() int {
	n := -1
	m := make(map[int]int, n)
	m[1] = 2
	return len(m)
}

// The hint is an ordinary operand: gc evaluates it (its side effects
// happen) and then ignores its value. BUG-082 (born red here, gc 31 vs
// machine 11): the native frontend did not lower the hint at all, so the
// bump below never ran in the machine. FIXED 2026-09-02 (bug082-maphint):
// the hint is lowered and evaluated; the wider family is
// builtins/make-map-hint-eval.
func makeMaxAllocMapHintEvalOrder() int {
	n := 1
	m := make(map[int]int, makeMaxAllocBump(&n))
	m[1] = 2
	return n*10 + len(m)
}

func makeMaxAllocBump(p *int) int {
	*p = *p + 2
	return *p
}

func makeMaxAllocRecoverSliceLen() (result int) {
	defer func() {
		if recover() != nil {
			result = 1
		}
	}()
	n := 1<<48 + 1
	_ = make([]byte, n)
	return 0
}

func makeMaxAllocRecoverChanSize() (result int) {
	defer func() {
		if recover() != nil {
			result = 1
		}
	}()
	n := 1 << 48
	_ = make(chan byte, n)
	return 0
}

func main() {
	makeMaxAllocSliceLenOverByte()
}
