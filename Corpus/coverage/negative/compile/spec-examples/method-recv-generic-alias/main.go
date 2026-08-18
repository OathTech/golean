// spec#Method_declarations block Method_declarations-4-fa8d3c1f: receiver denoted by alias: the alias must not be generic
package main

type Point struct{ x, y float64 }

type GPoint[P any] = Point

func (*GPoint[P]) Draw(P) {} // illegal: alias must not be generic

func main() {}
