// noodler probes — slice aliasing under append (spec#Appending_and_copying_slices:
// "If the capacity of s is not large enough ... append allocates a new
// underlying array"; otherwise the existing one is reused). Every
// observable here depends only on len-vs-cap, never on the new capacity
// (R2 latitude is not observed).
package main

// len == cap: append reallocates; the original is untouched.
func appendReallocatesAtCap() (int, int) {
	s := make([]int, 2, 2)
	t := append(s, 1)
	t[0] = 9
	return s[0], t[0]
}

// len < cap: append shares; writes through t are visible in s.
func appendSharesWithinCap() (int, int) {
	s := make([]int, 2, 3)
	t := append(s, 1)
	t[0] = 9
	return s[0], len(s)
}

// Appending to a prefix overwrites the following element in the base.
func appendToPrefixOverwrites() (int, int) {
	s := []int{1, 2, 3}
	u := append(s[:1], 5)
	return s[1], len(u)
}

// Appending to a slice of an array writes into the array.
func appendIntoArrayStorage() (int, int) {
	arr := [4]int{}
	s := arr[:2]
	s = append(s, 7)
	return arr[2], len(s)
}

// Full slice expression caps the capacity so append must reallocate.
func fullSliceForcesRealloc() (int, int) {
	s := []int{1, 2, 3}
	t := s[:1:1]
	t = append(t, 8)
	return s[1], t[1]
}

// Reslicing to zero length then appending reuses the backing array.
func resliceZeroThenAppend() int {
	s := []int{1, 2, 3}
	t := s[:0]
	t = append(t, 42)
	return s[0]
}

// A callee appending within capacity changes the caller's element but
// not the caller's length.
func calleeAppendWithinCap() (int, int) {
	s := make([]int, 1, 4)
	s[0] = 1
	grow := func(x []int) { x = append(x, 5); x[0] = 9 }
	grow(s)
	return s[0], len(s)
}

// The delete idiom leaves a duplicate tail in the backing array.
func deleteIdiomTail() (int, int, int) {
	s := []int{1, 2, 3, 4}
	orig := s[:4]
	s = append(s[:1], s[2:]...)
	// orig shares the backing array: [1 3 4 4] after the shift.
	return len(s), s[1]*10 + s[2], orig[1]*100 + orig[2]*10 + orig[3]
}

// Appending a slice to itself doubles it.
func appendSelfDoubles() (int, int) {
	s := []int{1, 2, 3}
	s = append(s, s...)
	return len(s), s[3]*100 + s[4]*10 + s[5]
}

// Byte slice from a string: sub-slices alias each other but not the
// string.
func byteSliceSubAlias() (string, string) {
	str := "hello"
	b := []byte(str)
	b2 := b[1:]
	b2[0] = 'a'
	return string(b), str
}

// Reslicing beyond len within cap exposes appended data.
func resliceBeyondLenSeesAppend() int {
	s := make([]int, 1, 3)
	_ = append(s, 7, 8)
	t := s[:3]
	return t[1]*10 + t[2]
}

// Slice of slice: the inner shares with the outer's window.
func nestedResliceShares() (int, int) {
	s := []int{0, 1, 2, 3, 4}
	a := s[1:4]
	b := a[1:]
	b[0] = 99
	return s[2], cap(b)
}

// Multiple appends chained in one expression, all within cap of the
// original.
func chainedAppendsWithinCap() (int, int) {
	s := make([]int, 0, 8)
	t := append(append(append(s, 1), 2), 3)
	u := append(s, 9)
	return t[0], len(t) + len(u)
}

// Copying a slice header (assignment) shares storage; append at cap on
// one does not move the other.
func headerCopyIndependence() (int, int, int) {
	s := make([]int, 1, 1)
	t := s
	t = append(t, 2)
	t[0] = 5
	s[0] = 7
	return s[0], t[0], len(t)
}

// Zero-length slice from make is non-nil; from var is nil; both append
// fine.
func nilVsEmptyAppend() (bool, bool, int, int) {
	var a []int
	b := make([]int, 0)
	a = append(a, 1)
	b = append(b, 1)
	return a == nil, b == nil, len(a), len(b)
}

// Slice of array pointer through a function parameter shares the array.
func arrayPointerSliceShares() int {
	arr := [3]int{1, 2, 3}
	set := func(p *[3]int) { s := p[1:]; s[0] = 20 }
	set(&arr)
	return arr[1]
}

func main() {}
