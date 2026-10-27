package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The PREPRINT rewrite (gc's preprintpanics: an `error` payload is printed as
// its Error(), a Stringer as its String()) when the method is PROMOTED — the
// machine's preprintDispatch resolves the record and walks its path: a value
// embed, a non-nil pointer embed, an embedded interface holding a value, and
// a pointer box whose promoted Error has a pointer receiver (the addr adjust).

type failure struct{ code int }

func (f failure) Error() string {
	if f.code == 1 {
		return "failure one"
	}
	return "failure other"
}

type wrapped struct{ failure }

func valueEmbedError() int {
	panic(wrapped{failure{code: 1}})
}

type pwrapped struct{ *failure }

func pointerEmbedError() int {
	panic(pwrapped{&failure{code: 2}})
}

type tag struct{}

func (tag) String() string { return "tagged" }

type stringer interface{ String() string }

type labelled struct{ stringer }

func embeddedIfaceStringer() int {
	panic(labelled{tag{}})
}

type pfailure struct{ code int }

func (p *pfailure) Error() string { return "pointer failure" }

type pbox struct{ pfailure }

func pointerBoxPromotedError() int {
	panic(&pbox{}) // *pbox's set holds Error through the value embed (addr adjust)
}

func main() {
	defer func() { recover() }()
	valueEmbedError()
}
