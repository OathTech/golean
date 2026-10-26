package main

// Control: the conversion to a pointer to an UNNAMED struct type — the
// frontend's FR-13 refusal by name, expected on both sides of the fix.
type A struct{ X, Y int }

func probe() int {
	a := A{1, 2}
	pu := (*struct{ X, Y int })(&a)
	if *pu == (struct{ X, Y int }{1, 2}) {
		return 1
	}
	return 0
}

func main() { println(probe()) }
