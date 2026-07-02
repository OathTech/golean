package main

type valueGetter[T any] interface {
	Get() T
}

type genericIntBox struct {
	v int
}

func (b genericIntBox) Get() int {
	return b.v
}

func genericInterfaceValue() int {
	var g valueGetter[int] = genericIntBox{v: 7}
	return g.Get()
}

func main() {
	genericInterfaceValue()
}
