package main

type tagDefinedA struct {
	X int `tag:"a"`
}

type tagDefinedB struct {
	X int `tag:"b"`
}

func structTagDefinedConversion() int {
	a := tagDefinedA{X: 7}
	b := tagDefinedB(a)
	return b.X
}
