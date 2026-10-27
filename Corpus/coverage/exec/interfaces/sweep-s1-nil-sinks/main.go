package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// UNTYPED NIL into INTERFACE slots (a nil interface: assignment after a value,
// `var error = nil`, an argument, a return, a map-literal key, a map store, a
// struct field) and the TYPED-NIL POINTER into an interface slot by argument
// and by return (the classic non-nil `error`), beside BUG-016's slice / map /
// pointer sinks and the typed-nil `var` rows.

type tErr struct{}

func (*tErr) Error() string { return "tErr" }

type sPair struct {
	A any
	B error
}

func isNil(x any) bool { return x == nil }

func isNilErr(e error) bool { return e == nil }

func mkNil() error { return nil }

func mkTypedNil() error {
	var p *tErr = nil
	return p
}

func assignNilAfterValue() (bool, any) {
	var x any = 3
	x = nil
	return x == nil, x
}

func varErrorNil() bool {
	var e error = nil
	return e == nil
}

func argNilAny() (bool, any) {
	return isNil(nil), nil
}

func argTypedNilError() bool {
	var p *tErr
	return isNilErr(p)
}

func returnNilError() bool {
	return mkNil() == nil
}

func returnTypedNilPointer() (bool, string) {
	e := mkTypedNil()
	return e == nil, e.Error()
}

func mapLitNilKey() (int, bool) {
	m := map[any]int{nil: 1, "a": 2}
	v, ok := m[nil]
	return v, ok
}

func mapStoreNilValue() (bool, bool) {
	m := map[string]any{}
	m["k"] = nil
	_, ok := m["k"]
	return ok, m["k"] == nil
}

func structFieldNil() (bool, bool) {
	p := sPair{A: nil, B: nil}
	return p.A == nil, p.B == nil
}

func structFieldTypedNil() bool {
	var e *tErr
	p := sPair{B: e}
	return p.B == nil
}

func main() {
	assignNilAfterValue()
}
