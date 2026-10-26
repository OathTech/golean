package main

// Two empty struct types: convertible; the boxes differ by dynamic type.
type E1 struct{}
type E2 struct{}

func probe() int {
	e := E1{}
	pe := (*E2)(&e)
	r := 0
	if *pe == (E2{}) {
		r += 100
	}
	if any(*pe) == any(E2{}) {
		r += 10
	}
	if any(*pe) == any(E1{}) {
		r += 1
	}
	return r
}

func main() { println(probe()) }
