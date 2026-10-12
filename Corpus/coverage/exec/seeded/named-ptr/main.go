package main

// Seeded-heap slice C fix round (review MEDIUM-1, 2026-10-12): a seed
// reference bound at a NAMED pointer parameter type. The machine reads the
// parameter's underlying type (a pointer); the Go twin decides pointer-ness by
// reflect at run time and converts the reference to P — neither side reads
// the spelling.

type P *int

func viaNamed(p P) int {
	*p = *p + 1
	return *p
}

func main() {
	c0 := new(int)
	*c0 = 5
	println(viaNamed(c0), *c0)
}
