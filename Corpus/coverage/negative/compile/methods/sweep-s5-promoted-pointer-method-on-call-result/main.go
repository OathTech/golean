package main

type inner struct{ n int }

func (i *inner) inc() { i.n++ }

type outer struct{ inner }

func make1() outer { return outer{} }

func main() {
	make1().inc() // promoted through a value embed: the pointer receiver needs &make1().inner
}
