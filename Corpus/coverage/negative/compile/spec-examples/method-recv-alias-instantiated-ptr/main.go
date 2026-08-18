// spec#Method_declarations block Method_declarations-4-fa8d3c1f: receiver alias must not denote instantiated type GPoint[int] (via pointer)
package main

type Point struct{ x, y float64 }

type GPoint[P any] = Point
type HPoint = *GPoint[int]

func (HPoint) Draw(int) {} // illegal: alias must not denote instantiated type GPoint[int] (spec's Draw(P) param written as int: P not in scope here)

func main() {}
