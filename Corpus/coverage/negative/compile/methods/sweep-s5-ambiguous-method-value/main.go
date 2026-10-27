package main

type ambA struct{}

func (ambA) m() int { return 1 }

type ambB struct{}

func (ambB) m() int { return 2 }

type ambC struct {
	ambA
	ambB
}

func main() {
	var c ambC
	f := c.m // ambiguous selector: a method VALUE, not a call
	_ = f
}
