package main

type mapCounter struct {
	n int
}

func (c *mapCounter) inc() {
	c.n++
}

func main() {
	m := map[string]mapCounter{"x": {n: 1}}
	m["x"].inc()
}
