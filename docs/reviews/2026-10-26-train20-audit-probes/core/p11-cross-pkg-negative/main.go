package main

import "sub"

// The negative half: main.C spells sub.A's fields identically, but the
// unexported x belongs to a different package — gc rejects the conversion.
// The frontend must refuse it as a type error (the predicate alone would say
// compatible: the wire's FieldDef carries no package).
type C struct {
	x int
	Y int
}

func probe() int {
	pa := sub.MkA()
	pc := (*C)(pa)
	return pc.x
}

func main() { println(probe()) }
