package main

type cnt struct{ n int }

func (c *cnt) inc() { c.n++ }

func main() {
	var x any = cnt{}
	x.(cnt).inc() // a type assertion's result is not addressable
}
