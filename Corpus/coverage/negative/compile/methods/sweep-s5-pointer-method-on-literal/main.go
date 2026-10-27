package main

type cnt struct{ n int }

func (c *cnt) inc() { c.n++ }

func main() {
	cnt{}.inc() // a composite literal is not addressable
}
