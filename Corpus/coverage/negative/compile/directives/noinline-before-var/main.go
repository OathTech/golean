package main

// BUG-127 fix round: a //go:noinline before a var declaration is
// «misplaced compiler directive» in gc; the frontend exported it.
//
//go:noinline
var x = 1

func main() { println(x) }
