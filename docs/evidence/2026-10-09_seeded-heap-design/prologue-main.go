package main

// [AGENT] seeded-heap design probe (2026-10-09): hand-written prologues; aliased vs distinct.
func seedAddNaiveAlias() (int, int) {
	var c0 [2]int
	c0[0] = 5
	c0[1] = 7
	addNaive(&c0, &c0)
	return c0[0], c0[1]
}

func seedAddNaiveDistinct() (int, int, int, int) {
	var c0, c1 [2]int
	c0[0] = 5
	c0[1] = 7
	c1[0] = 5
	c1[1] = 7
	addNaive(&c0, &c1)
	return c0[0], c0[1], c1[0], c1[1]
}

func seedSum2() (int, int, int) {
	var c0, c1 Node
	c0.v = 2
	c1.v = 3
	c0.next = &c1
	c1.next = &c0
	r := sum2(&c0)
	return r, c0.v, c1.v
}

func seedSwap2Alias() int {
	var c0 cell
	c0.val = 42
	swap2(&c0, &c0)
	return c0.val
}

func main() {
	a, b := seedAddNaiveAlias()
	println("addNaive aliased:", a, b)
	p, q, r, s := seedAddNaiveDistinct()
	println("addNaive distinct:", p, q, r, s)
	x, y, z := seedSum2()
	println("sum2 cyclic:", x, y, z)
	println("swap2 aliased:", seedSwap2Alias())
}
