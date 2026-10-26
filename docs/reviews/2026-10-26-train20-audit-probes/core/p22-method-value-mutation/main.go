package main

// A method value with a VALUE receiver bound through the converted pointer
// copies the receiver at binding time (spec#Method_values): a later write to
// the cell must not reach it; a pointer-receiver method value sees the write.
type A struct{ X, Y int }
type B struct{ X, Y int }

func (b B) Sum() int  { return b.X + b.Y }
func (b *B) PX() int  { return b.X }

func probe() int {
	a := A{1, 2}
	pb := (*B)(&a)
	f := pb.Sum
	g := pb.PX
	a.X = 10
	return f()*100 + g()
}

func main() { println(probe()) }
