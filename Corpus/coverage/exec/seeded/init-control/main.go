package main

// Seeded-heap slice C (2026-10-12; design docs/2026-10-09_seeded-heap-design.md §7):
// the G-R control program (GoLean/GoCore/SetupStatement.lean `initControl`: one
// global, an initializer writing it, a subject reading it), widened by one
// initializer ALLOCATION — so the seed's base b, the post-init allocator bound,
// is a run quantity (design D1), not the globals' count. Row `empty` runs the
// subject over the EMPTY seed (S4's erasure: the ordinary run, `seed: []`); row
// `global-plus-cell` reads the global, the init-allocated cell and seed cell 0.
// main() is the Go prologue the harness generates, written by hand.

var g int

var box *int

func init() {
	g = 7
	box = new(int)
	*box = 30
}

func F() int {
	return g
}

func addGlobals(p *int) int {
	*p = *p + g + *box
	return *p
}

func main() {
	c0 := new(int)
	*c0 = 5
	println(F(), addGlobals(c0), *c0)
}
