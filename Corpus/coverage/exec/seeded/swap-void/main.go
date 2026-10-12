package main

// Seeded-heap slice C: a subject with NO results — the observation is the seed
// key alone (values []): the swapped cells prove the mutation. (An unseeded
// ok row must return a value; a seeded one observes its cells.)

func swap(a, b *int8) {
	*a, *b = *b, *a
}

func main() {
	c0, c1 := new(int8), new(int8)
	*c0, *c1 = -1, 100
	swap(c0, c1)
	println(*c0, *c1)
}
