package main

// spec#Assignment_statements block Assignment_statements-2-4c295deb:
// the four assignment-target forms — a variable (x = 1), a pointer
// indirection (*p = f()), an index expression (a[i] = 23), and a
// PARENTHESIZED operand ((k) = <-ch, "same as: k = <-ch"; the spec:
// "Operands may be parenthesized"). Expected: x == 1, *p == f() == 6,
// a[2] == 23 (others untouched), k == 44.

func assignTargetForms() (int, int, int, int, int) {
	var x, target, k int
	p := &target
	a := []int{10, 20, 30}
	i := 2
	f := func() int { return 6 }
	ch := make(chan int, 1)
	ch <- 44

	x = 1
	*p = f()
	a[i] = 23
	(k) = <-ch // same as: k = <-ch
	return x, target, a[2], a[0] + a[1], k
}

func main() {
	assignTargetForms()
}
