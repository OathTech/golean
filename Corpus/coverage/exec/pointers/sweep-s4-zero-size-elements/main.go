package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): BUG-176 — the zero-size
// ELEMENT and FIELD address identity. gc gives every element of an array or
// slice of a zero-size type, and every zero-size field at the same offset
// of one struct, ONE address — stack or heap, deterministically, because the
// address is base + 0*i / base + offset (spec#Size_and_alignment_guarantees
// leaves it open: "Two distinct zero-size variables may have the same
// address"). The machine's `Loc` paths `.index base 0` / `.index base 1`
// and `.field base "A"` / `.field base "B"` are distinct canonical paths and
// `valueEq`'s pointer arm answers false, so every red row below answers the
// never-same member where gc realizes same — a sibling of BUG-170's R15
// latitude with a different realization (size-driven, not escape-driven).
// The two controls (fields separated by a non-zero field; the same final
// field of two distinct non-escaping variables) agree at birth.

type zsT struct{}

type adj struct {
	A zsT
	B zsT
	C [0]int
}
type sep struct {
	A zsT
	N int
	B zsT
}
type lead struct {
	N int
	A zsT
	B zsT
}
type finOne struct {
	N int
	A zsT
}

var keepS []zsT
var keepA [][0]int
var keepArr *[3]zsT
var keepAdj *adj
var keepLead *lead

func bit(b bool, w int) int {
	if b {
		return w
	}
	return 0
}

// Elements of a stack array of a zero-size type (gc 111).
func zsArrayElems() int {
	var arr [3]zsT
	return bit(&arr[0] == &arr[1], 1) + bit(&arr[0] == &arr[2], 10) + bit(&arr[1] != &arr[2], 100)
}

// The same through `any` boxes of `*zsT` (gc 1).
func zsArrayElemsBoxed() int {
	var arr [3]zsT
	return bit(any(&arr[0]) == any(&arr[1]), 1)
}

// A heap array's elements (gc 1).
func zsArrayElemsEscaped() int {
	keepArr = new([3]zsT)
	return bit(&keepArr[0] == &keepArr[2], 1)
}

// Through a pointer to the array (gc 1).
func zsArrayViaPointer() int {
	var arr [3]zsT
	p := &arr
	return bit(&p[0] == &arr[1], 1)
}

// `make([]zsT, 3)`: every element one address (gc 11 + 100 for the != control).
func zsSliceElems() int {
	s := make([]zsT, 3)
	return bit(&s[0] == &s[1], 1) + bit(&s[0] == &s[2], 10) + bit(&s[1] != &s[2], 100)
}

// The escaped backing likewise (gc 1).
func zsSliceElemsEscaped() int {
	keepS = make([]zsT, 2)
	return bit(&keepS[0] == &keepS[1], 1)
}

// A slice of `[0]int` (gc 11).
func zsSliceArray0Elems() int {
	t := make([][0]int, 2)
	keepA = make([][0]int, 2)
	return bit(&t[0] == &t[1], 1) + bit(&keepA[0] == &keepA[1], 10)
}

// A slice LITERAL's elements (gc 1).
func zsSliceLitElems() int {
	u := []zsT{{}, {}}
	return bit(&u[0] == &u[1], 1)
}

// Two element addresses as map keys: one entry (gc 1).
func zsSliceElemMap() int {
	s := make([]zsT, 3)
	m := map[*zsT]int{&s[0]: 1}
	m[&s[1]] = 2
	return len(m)
}

// Two ADJACENT zero-size fields at offset 0 (gc 11).
func zsFieldsAdjacent() int {
	var s adj
	return bit(&s.A == &s.B, 1) + bit(&s.A != &s.B, 10)
}

// The same through `any` boxes (gc 1).
func zsFieldsAdjacentBoxed() int {
	var s adj
	return bit(any(&s.A) == any(&s.B), 1)
}

// The same on the heap (gc 1).
func zsFieldsAdjacentEscaped() int {
	keepAdj = new(adj)
	return bit(&keepAdj.A == &keepAdj.B, 1)
}

// Two adjacent zero-size field addresses as map keys: one entry (gc 1).
func zsFieldsAdjacentMap() int {
	var s adj
	m := map[*zsT]int{&s.A: 1}
	m[&s.B] = 2
	return len(m)
}

// The padded FINAL pair `N int; A, B zsT` — both after the int, one address
// (gc 1); escaped likewise (gc 10).
func zsFieldsFinalPair() int {
	var s lead
	keepLead = new(lead)
	return bit(&s.A == &s.B, 1) + bit(&keepLead.A == &keepLead.B, 10)
}

// CONTROL (agrees): zero-size fields SEPARATED by a non-zero field sit at
// different offsets (gc 0).
func zsFieldsSeparated() int {
	var s sep
	return bit(&s.A == &s.B, 1)
}

// CONTROL (agrees): the padded final field of two distinct NON-ESCAPING
// variables (gc 0, stack-distinct like pointers/zero-size-address/stack-distinct).
func zsFinalSingleDistinctVars() int {
	var o1, o2 finOne
	return bit(&o1.A == &o2.A, 1)
}

func main() {
	println(zsArrayElems(), zsArrayElemsBoxed(), zsArrayElemsEscaped(), zsArrayViaPointer(),
		zsSliceElems(), zsSliceElemsEscaped(), zsSliceArray0Elems(), zsSliceLitElems(), zsSliceElemMap(),
		zsFieldsAdjacent(), zsFieldsAdjacentBoxed(), zsFieldsAdjacentEscaped(), zsFieldsAdjacentMap(),
		zsFieldsFinalPair(), zsFieldsSeparated(), zsFinalSingleDistinctVars())
}
