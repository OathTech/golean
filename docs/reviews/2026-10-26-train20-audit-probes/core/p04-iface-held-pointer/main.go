package main

// A converted pointer held in an interface and in a map[string]any, asserted
// back and dereferenced; the pointer box's dynamic type is *B.
type A struct{ X, Y int }
type B struct{ X, Y int }

func probe() int {
	a := A{1, 2}
	var i any = (*B)(&a)
	p := i.(*B)
	m := map[string]any{"k": (*B)(&a)}
	q := m["k"].(*B)
	r := 0
	if *p == (B{1, 2}) {
		r += 100
	}
	if *q == (B{1, 2}) {
		r += 10
	}
	switch i.(type) {
	case *A:
		r += 1
	case *B:
		r += 2
	}
	return r
}

func main() { println(probe()) }
