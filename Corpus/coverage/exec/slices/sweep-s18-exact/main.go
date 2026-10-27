package main

// S18 sweep — the EXACT sizes around the latitude: make (every form: cap is the operand, no
// rounding — gc's stack-allocated variable make keeps cap = n), append with no elements,
// the zeroed tail of a spilled backing (tape-invariant), new([N]T) and array capacities.
// Strict rows: the observation does not depend on any pick. Probe-verified go1.26.5, 2026-10-27.
type IS []int

//go:noinline
func idn(n int) int { return n }

// append with no elements returns its operand: still nil, cap 0
func appendNilNoElems() int {
	var s []int
	s = append(s)
	if s == nil {
		return cap(s) + 100
	}
	return cap(s)
}

// append with no elements onto a full slice: no spill, cap unchanged
func appendFullNoElems() int {
	s := make([]int, 3, 3)
	s = append(s)
	return cap(s)
}

// the spilled backing's tail past len reads as zero at EVERY capacity (tape-invariant: strict)
func zeroTail() int {
	s := make([]int, 100, 100)
	s = append(s, 7)
	t := s[len(s):cap(s)]
	for _, v := range t {
		if v != 0 {
			return 1
		}
	}
	return 0
}

// make with a run-time length ≤ 32 bytes (gc stack-allocates a [32]byte): cap is EXACTLY n
func makeVarSmall() int {
	s := make([]byte, idn(7))
	return cap(s)
}

// make with a run-time length past the stack threshold: cap exactly n
func makeVarBig() int {
	s := make([]byte, idn(100))
	return cap(s)
}

// make with run-time len and cap: both exact
func makeLenCapVar() int {
	s := make([]int, idn(2), idn(5))
	return cap(s)*10 + len(s)
}

// make([]T, 0, 0): cap 0
func make0cap0() int {
	s := make([]int, 0, 0)
	return cap(s) + len(s)
}

// make([]T, 0) is non-nil with cap 0
func make0NonNil() int {
	s := make([]int, 0)
	if s == nil {
		return -1
	}
	return len(s)*10 + cap(s)
}

// make of a zero-size element with a run-time length: cap exactly n
func makeZeroSizeVar() int {
	s := make([]struct{}, idn(9))
	return cap(s)
}

// make of a defined slice type: cap exact
func makeDefined() int {
	s := make(IS, 3)
	return cap(s)
}

// slicing a new([N]T): cap N
func newArraySlice() int {
	p := new([7]int)
	s := p[:2]
	return cap(s)
}

// cap of an array and of a pointer to it: N
func arrayCap() int {
	var a [5]int
	return cap(a) + cap(&a)*10
}
