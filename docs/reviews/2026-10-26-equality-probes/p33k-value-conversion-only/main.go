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
	b := B(a)
	println(b == B{1, 2}, A(b) == a, any(b) == any(B{1, 2}))
}
