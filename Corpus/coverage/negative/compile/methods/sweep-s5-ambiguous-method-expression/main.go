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
	f := ambC.m // ambiguous selector: a method EXPRESSION
	_ = f
}
