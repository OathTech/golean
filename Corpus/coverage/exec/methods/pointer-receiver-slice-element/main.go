package main

type sliceCounter struct {
	n int
}

func (c *sliceCounter) inc() {
	c.n++
}

func pointerReceiverSliceElement() int {
	xs := []sliceCounter{{n: 1}, {n: 4}}
	xs[0].inc()
	xs[1].inc()
	return xs[0].n*10 + xs[1].n
}

func main() {
	pointerReceiverSliceElement()
}
