package counter

// Counter pins the value/pointer receiver asymmetry across a package
// boundary: Inc mutates through a pointer receiver, Get copies.
type Counter struct {
	N int
}

func (c *Counter) Inc() {
	c.N++
}

func (c Counter) Get() int {
	return c.N
}
