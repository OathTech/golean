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

func main() {
	x := ri.Make(1)
	y := bi.Make(4)
	fmt.Println(int(x.Get()), int(y.Get()), ri.Is(x), ri.Is(y), bi.Is(y), bi.Is(x))
	try("concrete same-name", func() { var a any = ri.Q{Tag: 1}; bi.AssertQ(a) })
	try("red T -> blue anon iface", func() { bi.Assert(x) })
	try("red T -> red anon iface ok", func() { ri.Assert(x) })
	try("red T -> blue T", func() { var a any = ri.T(1); _ = a.(bi.T) })
	try("red T -> blue unexported anon", func() { bi.AssertUnexp(x) })
	try("anon src -> concrete", func() { s := ri.Src(); _ = s.(ri.W) })
	try("nil -> red anon", func() { ri.Assert(nil) })
	fmt.Printf("%%T: %T %T\n", x, ri.Src())
	var z any = struct{ F ri.T }{}
	fmt.Printf("%%T anon struct: %T\n", z)
	try("anon struct assert", func() { _ = z.(struct{ F bi.T }) })
}
