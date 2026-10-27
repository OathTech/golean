package main

type part struct{}

type whole struct {
	part
	*part // the embedded field name is part twice
}

func main() {}
