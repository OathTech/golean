package main

// spec#Composite_literals block Composite_literals-6-98e6a258: "the
// zero value for a slice or map type is not the same as an initialized
// but empty value of the same type" — &[]int{} points to an
// initialized, EMPTY, non-nil slice of length 0, while new([]int)
// points to an uninitialized NIL slice of length 0.
// Expected: *p1 != nil, len(*p1) == 0; *p2 == nil, len(*p2) == 0.

func complitEmptySliceVsNew() (bool, int, bool, int) {
	p1 := &[]int{}   // p1 points to an initialized, empty slice, length 0
	p2 := new([]int) // p2 points to an uninitialized slice with value nil, length 0
	return *p1 == nil, len(*p1), *p2 == nil, len(*p2)
}

func main() {
	complitEmptySliceVsNew()
}
