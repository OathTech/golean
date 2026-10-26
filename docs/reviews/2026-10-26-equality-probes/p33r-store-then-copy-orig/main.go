package main

func main() { run() }

type A struct{ X, Y int }
type B struct{ X, Y int }

func run() {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	c := a
	println(c.X)
}
