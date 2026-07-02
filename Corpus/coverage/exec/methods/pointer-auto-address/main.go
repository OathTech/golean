package main

type autoAddressCounter struct {
	n int
}

func (c *autoAddressCounter) inc() {
	c.n++
}

func pointerReceiverAutoAddress() int {
	c := autoAddressCounter{n: 1}
	c.inc()
	return c.n
}

func main() {
	pointerReceiverAutoAddress()
}
