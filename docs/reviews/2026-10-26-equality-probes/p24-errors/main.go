package main

import "errors"

func main() { run() }

var ErrSentinel = errors.New("sentinel")

type myErr struct{ code int }

func (e myErr) Error() string { return "my" }

func get(ok bool) error {
	if ok {
		return nil
	}
	return ErrSentinel
}

func run() {
	e1 := errors.New("a")
	e2 := errors.New("a")
	println(e1 == e2, e1 == e1, e1 != e2, e1.Error() == e2.Error())
	println(get(false) == ErrSentinel, get(true) == nil, get(false) != nil)
	var v1 error = myErr{1}
	var v2 error = myErr{1}
	var v3 error = myErr{2}
	println(v1 == v2, v1 == v3, v1 == myErr{1})
	m := map[error]int{}
	m[e1] = 1
	m[e2] = 2
	m[ErrSentinel] = 3
	m[v1] = 4
	m[v2] = 5
	println(len(m), m[e1], m[v1], m[nil])
	switch get(false) {
	case nil:
		println("nil")
	case ErrSentinel:
		println("sentinel")
	}
	var ea any = e1
	println(ea == e1, ea == any(e2), e1 == ea)
	j := errors.Join(e1, e2)
	println(j == nil, j != nil, errors.Unwrap(j) == nil)
	w := wrap{e1}
	println(errors.Unwrap(w) == e1, errors.Unwrap(w) == e2)
}

type wrap struct{ inner error }

func (w wrap) Error() string  { return "w" }
func (w wrap) Unwrap() error { return w.inner }
