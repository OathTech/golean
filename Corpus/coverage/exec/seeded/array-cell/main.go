package main

// Seeded-heap slice C: pointers into an ARRAY inside a struct cell. Cell 1 is
// a *int seeded to point at cell 0's a[1]. `elem-arg` passes &c0.a[1]
// (--arg-ref 0.a[1]) and increments through it; `elem-result` flips the bool
// and returns &p.a[2] (seedRef cell 0, path ["a",2]), reading through cell 1.

type Pair struct {
	a [3]int
	b bool
}

func inc(p *int) int {
	*p = *p + 1
	return *p
}

func third(p *Pair, q **int) (*int, int) {
	p.b = !p.b
	**q = **q * 2
	return &p.a[2], p.a[1]
}

func main() {
	var c0 Pair
	c0 = Pair{a: [3]int{1, 9, 3}, b: true}
	c1 := &c0.a[1]
	println(inc(&c0.a[1]))
	r, v := third(&c0, &c1)
	println(r == &c0.a[2], v, c0.b)
}
