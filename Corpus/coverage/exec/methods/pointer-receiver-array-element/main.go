package main

type arrayCounter struct {
	n int
}

func (c *arrayCounter) inc() {
	c.n++
}

func pointerReceiverArrayElement() int {
	xs := [2]arrayCounter{{n: 2}, {n: 5}}
	xs[0].inc()
	xs[1].inc()
	return xs[0].n*10 + xs[1].n
}

func main() {
	pointerReceiverArrayElement()
}
