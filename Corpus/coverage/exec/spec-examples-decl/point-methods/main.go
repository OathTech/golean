package main

// spec#Method_declarations block Method_declarations-2-2c71f0c0 (Length and
// Scale bind to *Point) + spec#Calls block Calls-4-6010d7a1: p.Scale(3.5) on
// an addressable Point VALUE is shorthand for (&p).Scale(3.5), so the
// mutation through the pointer receiver is visible in p afterwards.
// Adaptation, noted: math.Sqrt is outside corpus import norms (fmt/sync/
// slices) and is replaced by a local Newton sqrt with identical use.

type Point struct{ x, y float64 }

func sqrt(x float64) float64 { // stands in for math.Sqrt (see header)
	z := x
	for i := 0; i < 30; i++ {
		z = (z + x/z) / 2
	}
	return z
}

func (p *Point) Length() float64 {
	return sqrt(p.x*p.x + p.y*p.y)
}

func (p *Point) Scale(factor float64) {
	p.x *= factor
	p.y *= factor
}

func pointScale() float64 {
	var p Point
	p = Point{x: 3, y: 4}
	p.Scale(3.5)        // (&p).Scale(3.5): mutates p
	return p.x*10 + p.y // 105 + 14 = 119
}

func pointLength() float64 {
	p := Point{x: 3, y: 4}
	return p.Length() // 5
}
