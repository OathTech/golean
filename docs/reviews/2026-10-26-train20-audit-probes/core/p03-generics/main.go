package main

// Generic instantiations: a generic deref at T=B, a generic box at T=B, and a
// pointer conversion between two generic struct instantiations with identical
// underlying types.
type A struct{ X, Y int }
type B struct{ X, Y int }
type G[T any] struct{ V T }
type H[T any] struct{ V T }

func deref[T any](p *T) T { return *p }
func box[T any](p *T) any  { return *p }

func probe() int {
	a := A{1, 2}
	pb := (*B)(&a)
	g := G[int]{5}
	ph := (*H[int])(&g)
	r := 0
	if deref(pb) == (B{1, 2}) {
		r += 1000
	}
	if _, ok := box(pb).(B); ok {
		r += 100
	}
	if *ph == (H[int]{5}) {
		r += 10
	}
	if _, ok := box(ph).(H[int]); ok {
		r += 1
	}
	*ph = H[int]{8}
	return r*10 + g.V
}

func main() { println(probe()) }
