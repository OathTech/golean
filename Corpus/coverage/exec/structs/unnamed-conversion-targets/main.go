package main

// Conversions whose TARGET's resolved shape is an unnamed composite
// (pointer/slice/map/func) — the Go spec's own canonical examples
// ("(*Point)(p)", "(func() int)(x)", "(*int)(nil)"). The conversion
// kernel had arms only for int/float/string/defined/struct/interface
// targets, so this whole family refused — including the identity
// retag (*uctCell)(&c), the typed-nil idiom (*uctCell)(nil), and the
// defined->defined direction whose target resolves to a composite
// (uctInts(xs)). Arc-final audit F10 (2026-08-06), red-first.

type uctCell struct{ n int }

type uctInts []int

type uctM map[string]int

type uctFn func(int) int

func uctPointer() int {
	c := uctCell{5}
	p := (*uctCell)(&c)
	return p.n
}

func uctPointerNil() int {
	p := (*uctCell)(nil)
	if p == nil {
		return 1
	}
	return 0
}

func uctSlice() int {
	xs := uctInts{1, 2, 3}
	ys := []int(xs)
	return len(ys) + ys[2]
}

func uctSliceToDefined() int {
	ys := []int{4, 5}
	xs := uctInts(ys)
	return len(xs) + xs[0]
}

func uctMap() int {
	m := uctM{"a": 7}
	n := map[string]int(m)
	return n["a"]
}

func uctFunc() int {
	f := func(x int) int { return x * 2 }
	g := (func(int) int)(f)
	return g(21)
}

func uctDouble(x int) int { return x + x }

func uctFuncFromDefined() int {
	h := uctFn(uctDouble)
	k := (func(int) int)(h)
	return k(4)
}

// NIL conversions at slice/map targets (delta-review D3, 2026-08-06):
// the conversion must produce the machine's nil-SLICE/nil-MAP value
// (len 0, == nil), exactly what the typed nil literal produces — the
// first arms returned the raw machine nil, so len/append on the result
// failed. Pointer/func targets were already right (raw nil IS their
// representation, pinned by pointer-nil above).
func uctSliceNil() int {
	b := []byte(nil)
	xs := []int(nil)
	n := 0
	if b == nil {
		n += 100
	}
	if xs == nil {
		n += 10
	}
	xs = append(xs, 5)
	return n + len(b) + xs[0] - 4
}

func uctMapNil() int {
	m := map[string]int(nil)
	n := len(m)
	if m == nil {
		n += 10
	}
	return n + m["absent"]
}
