package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// BUG-079's site where the guard ADMITS: a comma-ok type assertion assigned
// (`=`) into interface-typed targets whose asserted component is itself an
// INTERFACE (interface-to-interface: the dynamic type is kept, no box is owed)
// — a narrower target, `any`, `error` — and the `:=` form beside it (the
// targets take the component types). The non-interface components into
// interface targets stay a named refusal (recorded as a coverage gap).

type tRW interface {
	R() int
	W() int
}

type tR interface{ R() int }

type tBoth struct{ n int }

func (b tBoth) R() int { return b.n }
func (b tBoth) W() int { return b.n * 2 }

type tErr struct{}

func (tErr) Error() string { return "tErr" }

func assertIfaceIntoNarrower() (int, bool) {
	var x any = tBoth{3}
	var r tR
	var ok bool
	r, ok = x.(tRW)
	if !ok {
		return -1, ok
	}
	return r.R(), ok
}

func assertIfaceIntoAny() (int, bool, bool) {
	var x any = tErr{}
	var e any = "before"
	var ok bool
	e, ok = x.(error)
	score := 0
	switch e.(type) {
	case tErr:
		score = 1
	}
	return score, ok, e == x
}

func assertIfaceMiss() (bool, bool) {
	var x any = 3
	var r tR = tBoth{1}
	var ok bool
	r, ok = x.(tRW)
	return r == nil, ok
}

func assertDefineForms() (int, bool, bool) {
	var x any = tBoth{5}
	rw, ok := x.(tRW)
	_, ok2 := x.(error)
	return rw.W(), ok, ok2
}

func main() {
	assertIfaceIntoNarrower()
}
