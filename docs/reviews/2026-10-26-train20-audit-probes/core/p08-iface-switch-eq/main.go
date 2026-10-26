package main

// An expression switch on an interface holding *pb against struct literals of
// both types, and interface inequality between the B box and the A box.
type A struct{ X, Y int }
type B struct{ X, Y int }

func probe() int {
	a := A{1, 2}
	pb := (*B)(&a)
	var i any = *pb
	r := 0
	switch i {
	case B{1, 2}:
		r += 100
	case A{1, 2}:
		r += 200
	}
	var j any = a
	switch j {
	case B{1, 2}:
		r += 10
	case A{1, 2}:
		r += 20
	}
	if i != j {
		r += 1
	}
	return r
}

func main() { println(probe()) }
