package main

// An outer struct embedding *A; the embedded pointer converted and
// dereferenced whole; the promoted field read through the outer afterwards.
type A struct{ X, Y int }
type B struct{ X, Y int }
type H struct {
	*A
	N int
}

func probe() int {
	a := A{1, 2}
	h := H{&a, 3}
	pb := (*B)(h.A)
	r := 0
	if *pb == (B{1, 2}) {
		r += 100
	}
	*pb = B{4, 5}
	return r + h.X*10 + h.Y
}

func main() { println(probe()) }
