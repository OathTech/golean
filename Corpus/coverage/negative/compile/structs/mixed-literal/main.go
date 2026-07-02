package main

type mixedLiteralStruct struct {
	x int
}

var _ = mixedLiteralStruct{1, x: 2}
