package main

// Write routes: a pointer-receiver method storing the whole value through the
// converted receiver, a swap between two cells of DIFFERENT mint tags through
// crossed aliases (value conversions on the right, as Go requires), and a
// value-receiver copy that must not touch the cell.
type A struct{ X, Y int }
type B struct{ X, Y int }

func (b *B) Reset(x int) { *b = B{x, x} }
func (b B) Copy() B      { b.X = 100; return b }

func probe() int {
	a := A{1, 2}
	b := B{3, 4}
	pb := (*B)(&a)
	pa := (*A)(&b)
	pb.Reset(5)
	r := a.X * 1000
	*pb, *pa = B(*pa), A(*pb)
	r += a.X*100 + b.X*10
	c := pb.Copy()
	if a.X == 3 && c.X == 100 {
		r += 1
	}
	return r
}

func main() { println(probe()) }
