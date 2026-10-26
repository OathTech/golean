package main

// The type switch binds a COPY of the boxed *pb: writing it leaves the cell
// alone; the B clause is taken.
type A struct{ X, Y int }
type B struct{ X, Y int }

func probe() int {
	a := A{1, 2}
	pb := (*B)(&a)
	r := 0
	switch v := any(*pb).(type) {
	case A:
		v.X = 7
		r = 1
	case B:
		v.X = 9
		r = 2 + v.X
	}
	return r*10 + a.X
}

func main() { println(probe()) }
