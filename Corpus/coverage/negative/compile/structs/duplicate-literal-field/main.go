package main

type duplicateLiteralFieldStruct struct {
	x int
}

var _ = duplicateLiteralFieldStruct{x: 1, x: 2}
