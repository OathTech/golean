package main

// Seeded-heap slice C: ALIASED vs DISTINCT pointer arguments into the seed
// (design §0 P1: addNaive(&c0,&c0) on 5 -> 20 20; on two cells 5, 7 -> 12 19).
// The seed key proves the final cells: one cell 20, or two cells 12 and 19.

func addNaive(a, b *int) (int, int) {
	*a = *a + *b
	*b = *a + *b
	return *a, *b
}

func main() {
	c0 := new(int)
	*c0 = 5
	x, y := addNaive(c0, c0)
	d0, d1 := new(int), new(int)
	*d0, *d1 = 5, 7
	u, v := addNaive(d0, d1)
	println(x, y, *c0, u, v, *d0, *d1)
}
