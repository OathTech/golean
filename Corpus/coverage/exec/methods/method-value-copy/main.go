package main

type counter struct {
	n int
}

func (c counter) get() int {
	return c.n
}

func methodValueCopy() int {
	c := counter{n: 1}
	bound := c.get
	c.n = 99
	return bound()*100 + c.get()
}
