package main

type boolOrInt interface {
	~bool | ~int
}

func andMixedBoolInt[T boolOrInt](a T, b T) bool {
	return a && b
}
