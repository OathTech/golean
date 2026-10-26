package main

// A func-typed field whose parameter NAMES differ between the two struct
// types: identical in Go (parameter names are not part of a signature's
// identity), so the pointer conversion is legal.
type A struct {
	F func(a int) int
	N int
}
type B struct {
	F func(b int) (r int)
	N int
}

func probe() int {
	a := A{func(x int) int { return x * 2 }, 1}
	pb := (*B)(&a)
	x := *pb
	r := x.F(3)*10 + x.N
	*pb = B{func(y int) int { return y + 100 }, 2}
	return r*1000 + a.F(1) + a.N
}

func main() { println(probe()) }
