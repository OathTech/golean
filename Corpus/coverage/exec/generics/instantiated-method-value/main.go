package main

type genericMethodBox[T any] struct {
	value T
}

func (b genericMethodBox[T]) Value() T {
	return b.value
}

func genericInstantiatedMethodValue() int {
	b := genericMethodBox[int]{value: 8}
	f := b.Value
	return f()
}
