package main

import (
	bi "blue/inner"
	"fmt"
	ri "red/inner"
	"reflect"
)

func try(name string, f func()) {
	defer func() { fmt.Printf("%s: %v\n", name, recover()) }()
	f()
}

type Pair[A any] struct{ A A }

func main() {
	var x any = ri.T(1)
	try("cross unexported single", func() { bi.AssertGet(x) })
	fmt.Println(ri.IsGet(x), bi.IsGet(x))
	fmt.Printf("%T\n", Pair[ri.T]{})
	// reflect.Type.Name() — the observation channel's contract — and
	// String() of the same instantiation (audit fix round R15, 2026-09-05:
	// the records credited this probe with a Name() line it did not have).
	fmt.Printf("Name()=%q String()=%q\n", reflect.TypeOf(Pair[ri.T]{}).Name(), reflect.TypeOf(Pair[ri.T]{}).String())
	var p any = Pair[ri.T]{A: 1}
	try("pair assert", func() { _ = p.(Pair[bi.T]) })
}
