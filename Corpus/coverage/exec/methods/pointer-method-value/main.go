package main

type pointerMethodValueCounter struct {
	n int
}

func (c *pointerMethodValueCounter) inc() {
	c.n++
}

func pointerMethodValue() int {
	c := pointerMethodValueCounter{n: 1}
	f := c.inc
	c.n = 10
	f()
	return c.n
}

func main() {
	pointerMethodValue()
}
