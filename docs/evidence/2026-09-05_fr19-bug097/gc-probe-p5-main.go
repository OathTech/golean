package main

import (
	bi "blue/inner"
	"fmt"
	ri "red/inner"
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
	var p any = Pair[ri.T]{A: 1}
	try("pair assert", func() { _ = p.(Pair[bi.T]) })
}
