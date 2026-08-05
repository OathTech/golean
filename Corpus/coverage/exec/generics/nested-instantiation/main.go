package main

type nestBox[T any] struct {
	v T
}

func nestMake[T any](x T) nestBox[T] {
	return nestBox[T]{v: x}
}

func genericNestedInstantiation() int {
	inner := nestMake(6)
	outer := nestMake(inner)
	deep := nestBox[nestBox[nestBox[int]]]{v: nestBox[nestBox[int]]{v: nestBox[int]{v: 3}}}
	return outer.v.v*10 + deep.v.v.v
}

func main() {
	genericNestedInstantiation()
}
