package main

type unknownFieldStruct struct {
	x int
}

var _ = unknownFieldStruct{y: 1}
