package main

// A generic type's method body is sized once the type is instantiated.
type G[T any] struct{}

func (G[T]) M() {
	var c chan [9000]T
	_ = c
}

func main() {
	var g G[int]
	_ = g
}
