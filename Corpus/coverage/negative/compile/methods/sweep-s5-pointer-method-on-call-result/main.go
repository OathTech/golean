package main

type cnt struct{ n int }

func (c *cnt) inc() { c.n++ }

func make1() cnt { return cnt{n: 1} }

func main() {
	make1().inc() // the CALL form of spec#Method_values' makeT().Mp
}
