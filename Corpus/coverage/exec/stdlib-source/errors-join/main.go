package main

// errors.Join through the REAL upstream body with the OVERLAID site
// (errors/join.go:58 `unsafe.String(&b[0], len(b))` -> `string(b)`;
// stdlib source-through slice 2, 2026-09-03). errors.New is the real
// library constructor too (its user-facing shim RETIRED this slice), so
// every error here is a real *errors.errorString / *errors.joinError.
// Rows pin the documented contract (godoc: Join discards nils, returns
// nil if every value is nil, formats as the newline-joined Error texts,
// implements Unwrap() []error) and the byte-identity the :58 overlay
// claims (the joined text with its embedded newlines).

import "errors"

func joinAllNil() (bool, bool, bool) {
	return errors.Join() == nil, errors.Join(nil) == nil, errors.Join(nil, nil, nil) == nil
}

func joinOne() (string, int, bool) {
	e1 := errors.New("only")
	j := errors.Join(nil, e1, nil)
	us := j.(interface{ Unwrap() []error }).Unwrap()
	return j.Error(), len(us), us[0] == e1
}

func joinMany() (string, int) {
	e1, e2, e3 := errors.New("alpha"), errors.New("beta"), errors.New("gamma")
	j := errors.Join(e1, nil, e2, e3)
	return j.Error(), len(j.Error())
}

func joinUnwrapIdentity() string {
	e1, e2 := errors.New("x"), errors.New("y")
	j := errors.Join(e1, e2)
	us := j.(interface{ Unwrap() []error }).Unwrap()
	out := ""
	for i, u := range us {
		if (i == 0 && u == e1) || (i == 1 && u == e2) {
			out += "="
		} else {
			out += "!"
		}
	}
	return out
}

func joinNested() string {
	inner := errors.Join(errors.New("a"), errors.New("b"))
	return errors.Join(inner, errors.New("c")).Error()
}

func joinEmptyTexts() (string, int) {
	j := errors.Join(errors.New(""), errors.New(""))
	return j.Error(), len(j.Error())
}

func joinDistinct() (bool, bool) {
	e := errors.New("same")
	j1, j2 := errors.Join(e), errors.Join(e)
	return j1 == j2, j1.Error() == j2.Error()
}

func newIsFresh() (bool, bool, string) {
	a, b := errors.New("t"), errors.New("t")
	return a == b, a == a, a.Error()+b.Error()
}

func main() {
	a, b, c := joinAllNil()
	println(a, b, c)
	s, n, ok := joinOne()
	println(s, n, ok)
	m, l := joinMany()
	println(m, l)
	println(joinUnwrapIdentity())
	println(joinNested())
	e, el := joinEmptyTexts()
	println(e, el)
	d1, d2 := joinDistinct()
	println(d1, d2)
	f1, f2, ft := newIsFresh()
	println(f1, f2, ft)
}
