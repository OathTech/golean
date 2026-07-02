package main

type pointerMethodExpressionCounter struct {
	n int
}

func (c *pointerMethodExpressionCounter) add(x int) {
	c.n += x
}

func pointerMethodExpression() int {
	c := pointerMethodExpressionCounter{n: 2}
	f := (*pointerMethodExpressionCounter).add
	f(&c, 5)
	return c.n
}

func main() {
	pointerMethodExpression()
}
