package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// spec#Selectors' DEPTH rule at the shapes the earlier rows did not hold: a
// depth-1 method resolves what would be ambiguous at depth 2 (direct call,
// satisfaction, dispatch, method expression, the explicit path to a shadowed
// deep method); a FIELD at depth 1 hides a METHOD at depth 2 (the type does
// not implement the interface; the explicit path still calls); a METHOD at
// depth 1 hides a FIELD at depth 2; a shallow method of the WRONG signature
// hides a deep one of the right signature (not satisfied).

type ambA struct{}

func (ambA) M() int { return 1 }

type ambB struct{}

func (ambB) M() int { return 2 }

type resolver struct {
	ambA
	ambB
}

func (resolver) M() int { return 3 } // depth 0 of resolver, depth 1 of wrap

type wrap struct{ resolver }

type mer interface{ M() int }

func depth1ResolvesDepth2() int {
	var w wrap
	a := w.M() // resolver.M at depth 1 wins over ambA.M / ambB.M at depth 2
	var i mer = w
	b := i.M()
	var x any = w
	_, ok := x.(mer)
	e := wrap.M
	c := e(w)
	d := w.resolver.ambB.M() // the explicit path reaches the shadowed one
	r := a*1000 + b*100 + c*10 + d
	if ok {
		r += 10000
	}
	return r
}

type deepM struct{}

func (deepM) x() int { return 7 }

type midF struct {
	deepM
	x int // a field at depth 1 of fh hides deepM.x at depth 2
}

type fh struct{ midF }

type xer interface{ x() int }

func fieldHidesDeeperMethod() int {
	h := fh{midF{x: 5}}
	var v any = h
	_, ok := v.(xer) // fh has no method x: the field shadows it
	r := h.x*10 + h.midF.deepM.x()
	if ok {
		r += 1000
	}
	return r
}

type deepF struct{ x int }

type midM struct{ deepF }

func (midM) x() int { return 9 } // a method at depth 1 of mh hides deepF.x at depth 2

type mh struct{ midM }

func methodHidesDeeperField() int {
	h := mh{midM{deepF{x: 4}}}
	var v any = h
	_, ok := v.(xer)
	r := h.x()*10 + h.midM.deepF.x
	if ok {
		r += 1000
	}
	return r
}

type rightSig struct{}

func (rightSig) M() int { return 11 }

type wrongSig struct{ rightSig }

func (wrongSig) M() string { return "s" } // the shallow M is the one in the set

type sh struct{ wrongSig }

func shallowWrongSignatureHidesDeep() int {
	var s sh
	var v any = s
	_, ok := v.(mer) // M() string is not M() int: not satisfied
	r := len(s.M()) + s.wrongSig.rightSig.M()*10
	if ok {
		r += 1000
	}
	return r
}

func main() {
	depth1ResolvesDepth2()
	fieldHidesDeeperMethod()
	methodHidesDeeperField()
	shallowWrongSignatureHidesDeep()
}
