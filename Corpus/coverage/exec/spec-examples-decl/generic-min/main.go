package main

// spec#Function_declarations block Function_declarations-3-9873b045: a
// generic function declaration with the constraint ~int|~float64 — the
// spec's min, which at package level SHADOWS the predeclared builtin min.
// Exercised at int, float64, and a named ~int member.

func min[T ~int | ~float64](x, y T) T {
	if x < y {
		return x
	}
	return y
}

type myInt int

func genericMin() int {
	a := min(2, 3)                      // 2
	b := min(4.5, 1.5)                  // 1.5
	c := min(myInt(9), myInt(4))        // 4
	return a*100 + int(b*2)*10 + int(c) // 234
}
