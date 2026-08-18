package main

// spec#Composite_literals block Composite_literals-9-bb382c43: "a
// slice literal describes the entire underlying array literal" — the
// form []T{x1, ..., xn} is shorthand for tmp := [n]T{x1, ..., xn};
// tmp[0 : n]. Expected: for the literal []int{7, 8, 9},
// len == cap == 3 and the elements are 7, 8, 9 — exactly what slicing
// the equivalent array yields; the two spellings are indistinguishable
// element-for-element and in len/cap.

func complitSliceIsArraySlice() (int, int, int, bool) {
	s := []int{7, 8, 9}
	tmp := [3]int{7, 8, 9}
	t := tmp[0:3]
	same := len(s) == len(t) && cap(s) == cap(t) &&
		s[0] == t[0] && s[1] == t[1] && s[2] == t[2]
	return len(s), cap(s), s[0]*100 + s[1]*10 + s[2], same
}

func main() {
	complitSliceIsArraySlice()
}
