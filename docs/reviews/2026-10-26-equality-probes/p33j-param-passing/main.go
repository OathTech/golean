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

func eqB(b B) bool { return b == B{1, 2} }

func run() {
	a := A{1, 2}
	pb := (*B)(&a)
	println(eqB(*pb))
}
