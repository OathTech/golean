package main

func main() { run() }

type A struct{ X, Y int }
type B struct{ X, Y int }

func run() {
	a := A{1, 2}
	pb := (*B)(&a)
	var i any = *pb
	_, isA := i.(A)
	v, isB := i.(B)
	println(isA, isB, v.X)
	switch i.(type) {
	case A:
		println("A")
	case B:
		println("B")
	}
}
