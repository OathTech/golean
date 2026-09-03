// noodler frontier probe — method expression (*Out).Get over a promoted
// VALUE-receiver method (the FR-3 deref-adapter shape, re-hit through
// promotion).
package main

type In struct{ n int }

func (i In) Get() int { return i.n }

type Out struct {
	In
	tag string
}

func promotedMethodExpressionPtr() int {
	g := (*Out).Get
	o := Out{In{4}, "t"}
	return g(&o)
}

func main() {}
