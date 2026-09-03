// noodler probes — the runtime's bounds-check panic texts across every
// slice/index shape (spec#Index_expressions, spec#Slice_expressions,
// spec#Run-time_panics: the messages are gc's realized strings, R9).
package main

func sliceHighPastCap(n int) int {
	s := make([]int, 2, 3)
	return len(s[:n])
}

func sliceLowPastHigh(n int) int {
	s := make([]int, 5)
	return len(s[n:2])
}

func sliceLowPastLen(n int) int {
	s := make([]int, 3, 8)
	return len(s[n:])
}

func threeIndexMaxPastCap(n int) int {
	s := make([]int, 2, 4)
	return cap(s[0:1:n])
}

func threeIndexHighPastMax(n int) int {
	s := make([]int, 5, 8)
	return cap(s[0:n:3])
}

func threeIndexLowPastHigh(n int) int {
	s := make([]int, 5, 8)
	return cap(s[n:2:4])
}

func stringSliceHighPastLen(n int) int {
	s := "abc"
	return len(s[:n])
}

func stringSliceLowPastHigh(n int) int {
	s := "abcdef"
	return len(s[n:2])
}

func stringIndexPastLen(n int) byte {
	s := "abc"
	return s[n]
}

func arraySliceHighPastLen(n int) int {
	a := [3]int{1, 2, 3}
	return len(a[:n])
}

func arrayPointerSliceHigh(n int) int {
	a := [3]int{1, 2, 3}
	p := &a
	return len(p[1:n])
}

func arrayPointerIndex(n int) int {
	a := [3]int{1, 2, 3}
	p := &a
	return p[n]
}

func indexNegativeViaVar(n int) int {
	s := []int{1, 2, 3}
	return s[n]
}

// Slicing past len but within cap is legal and exposes zeroed cells.
func sliceWithinCap() (int, int, int) {
	s := make([]int, 2, 5)
	s[0], s[1] = 7, 8
	t := s[:4]
	return len(t), t[2] + t[3], cap(t[1:])
}

// After reslicing up, an index that was out of range for s is fine
// for t.
func indexAfterReslice() int {
	s := make([]int, 1, 3)
	t := s[:3]
	t[2] = 9
	return t[2] + len(s)
}

// Slice of a nil slice with zero bounds is fine; s[0:0:0] too.
func nilSliceSlicing() (int, int, bool) {
	var s []int
	a := s[0:0]
	b := s[:0:0]
	return len(a), cap(b), a == nil
}

// An index expression on a slice element that is itself a slice.
func nestedIndexPanic(n int) int {
	ss := [][]int{{1}, {2, 3}}
	return ss[1][n]
}

// String index with a uint8 index type and a large constant-ish value.
func stringIndexUintKind(n int) byte {
	s := "hello"
	var i uint8 = uint8(n)
	return s[i]
}

// make with a negative len from a variable.
func makeNegativeLen(n int) int {
	s := make([]int, n)
	return len(s)
}

// Slice bounds where low == high == len is fine (empty slice at end).
func sliceAtEnd() (int, int) {
	s := []int{1, 2, 3}
	t := s[3:]
	u := s[3:3]
	return len(t), cap(u)
}

func main() {}
