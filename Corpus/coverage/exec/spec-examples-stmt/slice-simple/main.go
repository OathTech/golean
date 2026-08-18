package main

// spec#Slice_expressions block Slice_expressions-2-3678d32a: after
// a := [5]int{1, 2, 3, 4, 5}; s := a[1:4], the spec states: "the
// slice s has type []int, length 3, capacity 4, and elements
// s[0] == 2, s[1] == 3, s[2] == 4".

func sliceSimpleExpr() (int, int, int, int, int) {
	a := [5]int{1, 2, 3, 4, 5}
	s := a[1:4]
	return len(s), cap(s), s[0], s[1], s[2]
}

func main() {
	sliceSimpleExpr()
}
