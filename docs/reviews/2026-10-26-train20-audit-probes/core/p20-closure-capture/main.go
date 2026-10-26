package main

// A captured struct variable read inside a closure (the capture's own deref
// at type A) beside a captured converted pointer dereferenced whole, with the
// cell changing between calls.
type A struct{ X, Y int }
type B struct{ X, Y int }

func probe() int {
	a := A{1, 2}
	pb := (*B)(&a)
	f := func() int {
		x := a
		y := *pb
		if any(x) == any(A{a.X, a.Y}) && any(y) == any(B{a.X, a.Y}) {
			return x.X + y.Y
		}
		return -1
	}
	r := f()
	a.X = 10
	return r*100 + f()
}

func main() { println(probe()) }
