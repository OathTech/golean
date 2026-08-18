// spec#Method_declarations block Method_declarations-4-fa8d3c1f: receiver alias must not denote instantiated type Pair[int, int]
package main

type Pair[A, B any] struct {
	a A
	b B
}

type IPair = Pair[int, int]

func (*IPair) Second() int { return 0 } // illegal: alias must not denote instantiated type Pair[int, int]

func main() {}
