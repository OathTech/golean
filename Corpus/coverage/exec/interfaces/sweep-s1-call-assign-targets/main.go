package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// BUG-051's site at the other TARGETS and the other RESULT types: a
// single-value CALL assigned into an interface-typed struct field, slice
// element, array element, dereferenced pointer, map element, package-level
// variable and a parameter; a call returning a defined type, a typed-nil
// pointer, a narrower interface and an untyped-constant-typed value into an
// interface target; the same hoist-then-wrap at a compound target chain.

type tDef int

type tPt struct{ X int }

type tErr struct{}

func (*tErr) Error() string { return "tErr" }

type tRW interface {
	R() int
	W() int
}

type tR interface{ R() int }

type tBoth struct{ n int }

func (b tBoth) R() int { return b.n }
func (b tBoth) W() int { return b.n * 2 }

type sBox struct {
	V any
	E error
}

type sOuter struct{ In sBox }

var gAny any

func mkInt() int { return 11 }

func mkDef() tDef { return 3 }

func mkTypedNil() *tErr { return nil }

func mkRW() tRW { return tBoth{4} }

func fieldTarget() any {
	var b sBox
	b.V = mkInt()
	return b.V
}

func nestedFieldTarget() any {
	var o sOuter
	o.In.V = mkDef()
	return o.In.V
}

func sliceElemTarget() any {
	xs := make([]any, 2)
	xs[1] = mkInt()
	return xs[1]
}

func arrayElemTarget() any {
	var arr [2]any
	arr[0] = mkDef()
	return arr[0]
}

func derefTarget() any {
	var x any
	p := &x
	*p = mkInt()
	return x
}

func mapElemTarget() any {
	m := map[string]any{}
	m["k"] = mkInt()
	return m["k"]
}

func globalTarget() any {
	gAny = mkDef()
	return gAny
}

func paramTarget(x any) any {
	x = mkInt()
	return x
}

func paramTargetCall() any { return paramTarget("before") }

func typedNilResult() (bool, string) {
	var e error
	e = mkTypedNil()
	return e == nil, e.Error()
}

func typedNilIntoField() bool {
	var b sBox
	b.E = mkTypedNil()
	return b.E == nil
}

func narrowerResult() (int, bool) {
	var r tR
	r = mkRW()
	rw, ok := r.(tRW)
	if !ok {
		return -1, ok
	}
	return r.R() + rw.W(), ok
}

func definedResultAssert() int {
	var x any
	x = mkDef()
	if v, ok := x.(tDef); ok {
		return int(v) * 10
	}
	return 0
}

func main() {
	fieldTarget()
}
