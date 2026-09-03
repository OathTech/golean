// noodler frontier probe — implicit deref through a pointer field chain with assignment
package main

type C struct{ v int }
type B struct{ c *C }
type A struct{ b *B }

// Implicit pointer indirections through a field chain, including
// assignment (spec#Selectors: "x.f is shorthand for (*x).f").
func structPointerFieldChain() int {
	a := A{&B{&C{1}}}
	a.b.c.v += 4
	a.b.c = &C{a.b.c.v * 2}
	return a.b.c.v
}

func main() {}
