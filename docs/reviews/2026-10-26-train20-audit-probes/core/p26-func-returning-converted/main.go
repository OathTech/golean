package main

// The conversion inside a function; the caller dereferences the result whole,
// stores through it, and compares the pointer back.
type A struct{ X, Y int }
type B struct{ X, Y int }

func conv(p *A) *B { return (*B)(p) }

func probe() int {
	a := A{1, 2}
	r := 0
	if *conv(&a) == (B{1, 2}) {
		r += 100
	}
	*conv(&a) = B{3, 4}
	if (*A)(conv(&a)) == &a {
		r += 10
	}
	return r + a.X
}

func main() { println(probe()) }
