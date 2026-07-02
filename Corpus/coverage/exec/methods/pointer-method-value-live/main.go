package main

type liveMethodCell struct {
	n int
}

func (c *liveMethodCell) get() int {
	return c.n
}

func pointerMethodValueLive() int {
	c := &liveMethodCell{n: 1}
	f := c.get
	c.n = 7
	return f()
}
