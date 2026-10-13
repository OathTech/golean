package main

import _ "embed"

// BUG-127: gc rejects the package when the embed pattern matches no
// file («pattern data.txt: no matching files found»); the frontend
// exported it and the model answered 0 before the directive refusal.
//
//go:embed data.txt
var x string

func main() { println(len(x)) }
