package main

type Cloner[T any] interface {
	Clone() T
}

func use[T Cloner[T]](x T) T {
	return x.Clone()
}

type bad struct{}

func (bad) Clone() int {
	return 0
}

var _ = use[bad]
