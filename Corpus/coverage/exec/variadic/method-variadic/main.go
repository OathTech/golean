package main

type gatherer struct{ base int }

func (g gatherer) sum(xs ...int) int {
	total := g.base
	for i := 0; i < len(xs); i++ {
		total = total*10 + xs[i]
	}
	return total
}

func methodVariadic() int {
	g := gatherer{base: 1}
	return g.sum(2, 3) + g.sum()
}

func main() {
	methodVariadic()
}
