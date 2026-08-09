package main

// Observation-channel kind fidelity (grossmith hunt F15, spec-parity
// slice 1): every subject here lands a value that is NUMERICALLY
// IDENTICAL across integer kinds, so a kind-defaulting bug (the
// BUG-042/043 family: a synthetic literal or desugared variable
// silently taking the default int kind) that still computes the right
// number is INVISIBLE to a value-only observation channel. These cases
// pin the observation SHAPE family: once the channel carries
// {"kind":...} symmetrically (machine goValueJson + Go harness
// reflect kind), a wrong-kind-right-value machine answer diverges
// loudly. The in-range increment on a narrow kind is BUG-042's exact
// template (defInt8(5)++ == 6 whether the add ran at int8 or the
// defaulted int).

type obsUint8 uint8

func obsKindUint8() uint8 {
	v := uint8(5)
	v++ // 6 at uint8 AND at a kind-defaulted int: value-blind, kind-visible
	return v
}

func obsKindInt8Negative() int8 {
	v := int8(-4)
	v-- // -5 in-range for every signed kind
	return v
}

func obsKindDefinedUint8() obsUint8 {
	v := obsUint8(5)
	v++
	return v // reflect Kind()/Name(): kind uint8; the value carries no defined-type identity
}

func obsKindUint64Max() uint64 {
	v := uint64(0)
	v-- // wraps to 18446744073709551615: pins the unsigned upper range
	return v
}

type obsPair struct {
	A uint16
	B int32
}

func obsKindStructFields() obsPair {
	return obsPair{A: 7, B: 7} // same number, two kinds, recursed through struct fields
}

func obsKindBoxed() any {
	var v uint16 = 9
	return v // interface box: dynamic name "uint16" AND the boxed value's kind
}
