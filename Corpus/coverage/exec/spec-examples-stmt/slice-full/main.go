package main

// spec#Slice_expressions block Slice_expressions-7-6feb1778: the full
// slice expression a[low:high:max] has the same length and elements
// as a[low:high] and capacity max - low. After
// a := [5]int{1, 2, 3, 4, 5}; t := a[1:3:5], the spec states: "the
// slice t has type []int, length 2, capacity 4, and elements
// t[0] == 2, t[1] == 3".

func sliceFullExpr() (int, int, int, int) {
	a := [5]int{1, 2, 3, 4, 5}
	t := a[1:3:5]
	return len(t), cap(t), t[0], t[1]
}

func main() {
	sliceFullExpr()
}
