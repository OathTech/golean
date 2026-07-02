package main

type autoDerefCounter struct {
	n int
}

func (c autoDerefCounter) value() int {
	return c.n
}

func valueReceiverAutoDeref() int {
	c := &autoDerefCounter{n: 7}
	return c.value()
}

func main() {
	valueReceiverAutoDeref()
}
