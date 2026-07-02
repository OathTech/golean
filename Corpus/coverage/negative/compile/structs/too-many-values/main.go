package main

type tooManyValuesStruct struct {
	x int
}

var _ = tooManyValuesStruct{1, 2}
