package main

func main() { run() }

type B struct {
	_ int
	X int
}

var n int

func v(i int) int { n++; return i }

func run() {
	a := B{v(1), 2}
	b := B{v(3), 2}
	println(a == b, n)
}
