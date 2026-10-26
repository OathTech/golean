package main

func main() { run() }

type A struct{ X, Y int }
type B struct{ X, Y int }

func run() {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	var i any = a
	switch v := i.(type) {
	case B:
		println("B", v.X)
	case A:
		println("A", v.X)
	}
	println(pb.X, a.X, i == any(A{9, 9}))
}
