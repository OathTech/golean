package main

// DC01 neighbourhood: REFERENCE identity (channels, maps) read through
// the alias. A channel value is a reference to its payload cell (always a
// root cell), so `a.ch == b.ch` is base equality and agreed before the
// fix; distinct `make`s stay distinct; nil-ness of a map field is the
// same through either spelling. Rows pin the route beside the fixed ones.

type refA struct {
	ch chan int
	m  map[int]int
}
type refB struct {
	ch chan int
	m  map[int]int
}

func chanThroughAlias() bool {
	a := refA{ch: make(chan int)}
	b := (*refB)(&a)
	return a.ch == b.ch
}

func chanDistinctMakes() bool {
	a := refA{ch: make(chan int)}
	c := refA{ch: make(chan int)}
	return a.ch == c.ch
}

func chanBoxedThroughAlias() bool {
	a := refA{ch: make(chan int)}
	b := (*refB)(&a)
	return any(a.ch) == any(b.ch)
}

func mapNilThroughAlias() bool {
	a := refA{}
	b := (*refB)(&a)
	return a.m == nil && b.m == nil
}

func main() { println(chanThroughAlias(), chanDistinctMakes(), chanBoxedThroughAlias(), mapNilThroughAlias()) }
