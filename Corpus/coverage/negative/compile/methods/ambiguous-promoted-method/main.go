package main

type promotedA struct{}

func (promotedA) m() {}

type promotedB struct{}

func (promotedB) m() {}

type promotedC struct {
	promotedA
	promotedB
}

func main() {
	var c promotedC
	c.m()
}
