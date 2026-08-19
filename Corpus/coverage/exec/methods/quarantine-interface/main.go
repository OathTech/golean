package main

import "fmt"

// The fail-closed invariant of H-3: a quarantined method is NEVER dropped
// from its type's method set. Dropping it would change INTERFACE
// SATISFACTION — `item` would stop satisfying `stringer`, which it does
// satisfy in Go — and a comma-ok assert would then answer a silently wrong
// `false`. The stub carries the real signature, so satisfaction answers
// what gc answers and only the dispatched CALL refuses.

type stringer interface {
	tag() int
	render() string
}

type item struct{ n int }

func (i item) tag() int { return i.n * 2 }

func (i item) render() string { return fmt.Sprintf("item(%d)", i.n) }

func quarantineIfaceSatisfies() int {
	var x any = item{n: 3}
	if _, ok := x.(stringer); ok {
		return 1
	}
	return 0
}

func quarantineIfaceDispatchGood() int {
	var s stringer = item{n: 3}
	return s.tag()
}

func quarantineIfaceDispatchBad() int {
	var s stringer = item{n: 3}
	return len(s.render())
}

func main() {
	println(quarantineIfaceSatisfies(), quarantineIfaceDispatchGood(), quarantineIfaceDispatchBad())
}
