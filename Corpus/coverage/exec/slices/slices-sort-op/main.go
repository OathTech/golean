package main

// The `sortSlice` MACHINE OP's shapes (2026-10-25, backlog row 50, lane
// frontend/g19-sort-intercept-1025): a DIRECT `slices.Sort(s)` in
// expression-statement position at an INTEGER element kind lowers to the
// op (`sort-slice`) again — a deliberate partial reversal, for integer
// kinds, of memo §3 row M — while every other shape stays the real
// generic. The op reads the visible window, sorts the elements by their
// normalized integer value and writes the sorted run back IN PLACE; so
// the rows here pin what "in place" means against gc: a second header over
// the same backing array sees the sort, the spare capacity beyond `len` is
// untouched, a deferred sort (the generic path) agrees, a defined kind and
// `uintptr` sort through their underlying, `int8` negatives sort first, and
// a sort inside `init()` runs at package initialization.

import "slices"

// Two headers over ONE backing array: the sort through the window `s`
// (indices 1..4 of the array) is visible through the whole-array header
// `t`; the elements outside the window keep their places.
func sortAliasTwoHeaders() int {
	arr := [6]int{9, 7, 5, 3, 1, 8}
	s := arr[1:5]
	t := arr[:]
	slices.Sort(s)
	// arr = [9 1 3 5 7 8]
	return t[0]*100000 + t[1]*10000 + t[2]*1000 + t[3]*100 + t[4]*10 + t[5]
}

// Spare capacity: `s` has len 3 and cap 6; the three elements beyond `len`
// (reachable through `full`) are NOT part of the sort and keep their
// values and places.
func sortSpareCapacity() int {
	s := make([]int, 3, 6)
	s[0], s[1], s[2] = 3, 1, 2
	full := s[:6]
	full[3], full[4], full[5] = 9, 8, 7
	slices.Sort(s)
	// full = [1 2 3 9 8 7]; len(s) and cap(s) unchanged
	return full[0]*100000 + full[1]*10000 + full[2]*1000 + full[3]*100 + full[4]*10 + full[5] +
		len(s)*1000000 + cap(s)*10000000
}

// An empty window with spare capacity: nothing is read or written, the
// elements beyond `len` are untouched.
func sortEmptyWindowSpareCapacity() int {
	s := make([]uint8, 0, 4)
	full := s[:4]
	full[0], full[1], full[2], full[3] = 4, 3, 2, 1
	slices.Sort(s)
	return int(full[0])*1000 + int(full[1])*100 + int(full[2])*10 + int(full[3]) + len(s)*10000 + cap(s)*100000
}

// A DEFERRED sort at an integer kind is the generic path (the function
// value `slices.Sort[[]uint8,uint8]` with its pdqsort closure, not the op);
// its result agrees with the op's, read after it ran (LIFO).
func sortDeferredGeneric() (out int) {
	s := []uint8{200, 3, 100, 7}
	defer func() { out = int(s[0])*1000000 + int(s[1])*10000 + int(s[2])*100 + int(s[3]) }()
	defer slices.Sort(s)
	return
}

// A DEFINED integer kind over uint64 with values above 2^63: sorted through
// the underlying's UNSIGNED order (the normalized Lean Int is non-negative
// for unsigned kinds).
type nodeID uint64

func sortNamedUnsignedKind() uint64 {
	const top = ^uint64(0)
	ids := []nodeID{nodeID(top), 2, nodeID(1 << 63), 1}
	slices.Sort(ids)
	n := uint64(0)
	if ids[0] == 1 {
		n += 1000
	}
	if ids[1] == 2 {
		n += 100
	}
	if ids[2] == nodeID(1<<63) {
		n += 10
	}
	if ids[3] == nodeID(top) {
		n++
	}
	return n
}

// `uintptr` is an integer kind of its own (BUG-124): the op sorts it.
func sortUintptr() int {
	ps := []uintptr{30, 10, 20}
	slices.Sort(ps)
	return int(ps[0])*10000 + int(ps[1])*100 + int(ps[2])
}

// `int8`: the most negative value sorts first, the most positive last.
func sortInt8Negatives() int {
	xs := []int8{5, -128, 127, 0, -1}
	slices.Sort(xs)
	n := 0
	if xs[0] == -128 {
		n += 10000
	}
	if xs[1] == -1 {
		n += 1000
	}
	if xs[2] == 0 {
		n += 100
	}
	if xs[3] == 5 {
		n += 10
	}
	if xs[4] == 127 {
		n++
	}
	return n
}

// Duplicates: equal values are indistinguishable, so the result is the
// unique sorted sequence.
func sortDuplicates() int {
	xs := []int{2, 1, 2, 1, 2}
	slices.Sort(xs)
	return xs[0]*10000 + xs[1]*1000 + xs[2]*100 + xs[3]*10 + xs[4]
}

// The op inside `init()`: a package-level slice sorted at initialization.
var initSorted = []int{30, 10, 20}

func init() {
	slices.Sort(initSorted)
}

func sortInInit() int {
	return initSorted[0]*10000 + initSorted[1]*100 + initSorted[2]
}
