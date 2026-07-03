package main

func first[A any, B any](a A, b B) A {
	_ = b
	return a
}

var _ = first[int]
