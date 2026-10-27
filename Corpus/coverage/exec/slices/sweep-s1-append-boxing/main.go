package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// APPEND ELEMENTS into an interface-element slice beyond the spec example's
// (42, 3.1415, "foo"): a rune, a bool and nil; a defined value, a typed-nil
// pointer and an interface value; concrete values into a NARROWER interface
// element type.

type tDef int

func (d tDef) Val() int { return int(d) }

type tPt struct{ X int }

type tErr struct{}

func (tErr) Error() string { return "tErr" }

type tR interface{ R() int }

type tBoth struct{ n int }

func (b tBoth) R() int { return b.n }

func constsAndNil() (any, any, bool, any, int) {
	var xs []any
	xs = append(xs, 'c', true, nil, 2.5)
	return xs[0], xs[1], xs[2] == nil, xs[3], len(xs)
}

func typed() int {
	var p *tPt
	var e error = tErr{}
	xs := []any{"seed"}
	xs = append(xs, tDef(1), p, e)
	r := 0
	if v, ok := xs[1].(tDef); ok {
		r += v.Val()
	}
	if v, ok := xs[2].(*tPt); ok && v == nil {
		r += 10
	}
	if _, ok := xs[3].(tErr); ok {
		r += 100
	}
	return r
}

func narrower() int {
	rs := append([]tR{}, tBoth{1}, tBoth{2})
	rs = append(rs, tBoth{3})
	return rs[0].R() + rs[1].R()*10 + rs[2].R()*100
}

func main() {
	constsAndNil()
}
