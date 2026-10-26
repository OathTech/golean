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
	m := map[B]int{{1, 2}: 1}
	println(m[*pb], len(m))
	m[*pb] = 2
	println(m[B{1, 2}], len(m))
}
