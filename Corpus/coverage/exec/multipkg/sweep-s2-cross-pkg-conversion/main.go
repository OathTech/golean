package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The struct VALUE conversion across a package boundary (the train-20 audit's
// p11 holds the pointer route): the source type is found by its qualified tag.

import "sub"

type B struct{ X, Y int }
type C struct {
	Inner sub.A
}
type D struct {
	Inner sub.A
}

func (b B) Sum() int { return b.X + b.Y }

func crossPkgValueConversion() int {
	a := sub.MakeA(1)
	b := B(a)
	back := sub.A(b)
	var i any = b
	var j any = back
	r := 0
	switch i.(type) {
	case sub.A:
		r = 1
	case B:
		r = 2
	}
	if _, ok := j.(sub.A); ok {
		r += 10
	}
	c := C{Inner: a}
	d := D(c)
	var xs sub.Ints = []int{1, 2, 3}
	return r*10000 + b.Sum()*1000 + d.Inner.Y*100 + len(sub.Ints(xs))*10 + len(xs)
}

func main() {}
