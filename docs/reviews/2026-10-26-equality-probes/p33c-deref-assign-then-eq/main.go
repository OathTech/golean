package main

func main() { run() }

type A struct{ X, Y int }
type B struct{ X, Y int }
type In struct{ V int }
type OA struct {
	I In
	N int
}
type OB struct {
	I In
	N int
}

func run() {
	a := A{1, 2}
	pb := (*B)(&a)
	x := *pb
	println(x == B{1, 2}, x.X == 1)
}
