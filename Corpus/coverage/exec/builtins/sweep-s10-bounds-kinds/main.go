package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: the bounds panic
// (spec#Index_expressions, #Slice_expressions, #Conversions) at the index
// KINDS and slice FORMS noodler/bounds and slices/* do not pin — an int8 and an
// int64 index, a constant string indexed by a variable, the three-index form
// on an array and on a pointer to array, a negative low bound, a uint high past
// the capacity, a nil slice's high past its zero capacity, the slice-to-ARRAY-
// POINTER conversion (short slice panics; a nil slice converts to a nil *[0]T).

const bkConst = "abc"

func indexInt8Negative(z int) int {
	s := []int{1, 2}
	i := int8(z)
	return s[i]
}

func indexInt64PastLen(z int) int {
	s := []int{1, 2}
	i := int64(z)
	return s[i]
}

func constStringIndex(z int) int {
	return int(bkConst[z])
}

func arrayThreeIndexMaxPastLen(z int) int {
	a := [3]int{1, 2, 3}
	s := a[1:2:z]
	return len(s)
}

func arrayPtrThreeIndexHighPastMax(z int) int {
	p := &[3]int{1, 2, 3}
	s := p[1:z:3]
	return len(s)
}

func sliceNegativeLow(z int) int {
	s := []int{1, 2, 3}
	t := s[z:]
	return len(t)
}

func sliceHighUintPastCap(z int) int {
	s := []int{1, 2, 3}
	u := uint(z)
	t := s[:u]
	return len(t)
}

func nilSliceHighPastCap(z int) int {
	var s []int
	t := s[0:z]
	return len(t)
}

func sliceToArrayPtrShort() int {
	s := []int{1, 2}
	p := (*[4]int)(s)
	return p[0]
}

func nilSliceToZeroArrayPtr() int {
	var s []int
	p := (*[0]int)(s)
	if p == nil {
		return 1
	}
	return 0
}

func main() {}
