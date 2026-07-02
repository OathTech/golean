package main

type badRecursiveValue struct {
	next badRecursiveValue
}
