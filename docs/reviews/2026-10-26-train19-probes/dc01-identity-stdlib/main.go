package main

import "slices"

// BUG-133's local space through lowered library code: slices.Index / slices.Contains
// compare with == inside the lowered stdlib source, so they reach valueEq's pointer arm.

type tagA struct {
	X int `json:"a"`
}
type tagB struct {
	X int `json:"b"`
}

func containsThroughAlias() bool {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	return slices.Contains([]*int{&a.X}, &b.X)
}

func indexThroughAlias() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	c := tagA{X: 7}
	return slices.Index([]*int{&c.X, &a.X}, &b.X)
}

func main() { println(containsThroughAlias(), indexThroughAlias()) }
