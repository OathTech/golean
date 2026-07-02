package main

type oneParamBox[T any] struct {
	value T
}

var _ oneParamBox[int, string]
