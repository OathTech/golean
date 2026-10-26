package main

// Two holders of the converted pointer compare equal (pointer identity under
// the alias); a holder of &a boxed does not equal a holder of (*B)(&a) boxed.
type A struct{ X, Y int }
type B struct{ X, Y int }
type HB struct{ P *B }
type HA struct{ P *A }

func probe() int {
	a := A{1, 2}
	h1 := HB{(*B)(&a)}
	h2 := HB{(*B)(&a)}
	g := HA{&a}
	r := 0
	if h1 == h2 {
		r += 10
	}
	if any(h1) == any(g) {
		r += 1
	}
	return r
}

func main() { println(probe()) }
