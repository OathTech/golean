// noodler frontier probe — method expression over a promoted method (Out.Get / (*Out).Get)
package main

type In struct{ n int }

func (i In) Get() int { return i.n }

type Out struct {
	In
	tag string
}

// Method expression naming a PROMOTED method: Out.Get (spec#Method_expressions).
func promotedMethodExpression() int {
	f := Out.Get
	o := Out{In{4}, "t"}
	return f(o) * 10
}

func main() {}
