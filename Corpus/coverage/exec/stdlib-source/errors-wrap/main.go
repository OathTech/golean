package main

// errors.{Is,As,Unwrap} through the REAL library source (stdlib source-
// through slice 1, audit fix round B2, 2026-09-03). `errors` is a
// source-through library unit; its wrap.go bodies dispatch on UNNAMED
// interface types (`err.(interface{ Unwrap() error })`) and, for
// errors.As, reach internal/reflectlite (`reflectlite.TypeOf(target)`).
// godoc:errors.Is@go1.26.5 / godoc:errors.As@go1.26.5 /
// godoc:errors.Unwrap@go1.26.5. The audit found a program calling these
// killed the WHOLE export ("no declaration site"); the fix makes the
// interface-method edge inert. Whatever each body can lower is compared
// against gc; what cannot refuses BY NAME at its declaration and is a
// frontier red on FR-21's Cases: errors.Is (reflectlite.TypeOf(target).
// Comparable()) and errors.As (reflectlite.ValueOf/TypeOf) are BORN RED;
// errors.Unwrap is green. Remedy: the modeled reflect subset (memo G6).

import (
	"errors"
	"strconv"
)

type wrapped struct{ inner error }

func (w wrapped) Error() string { return "w:" + w.inner.Error() }
func (w wrapped) Unwrap() error { return w.inner }

func errorsUnwrap() (bool, bool, string) {
	_, err := strconv.ParseUint("x", 10, 64)
	w := wrapped{err}
	return errors.Unwrap(w) == err, errors.Unwrap(err) == strconv.ErrSyntax, errors.Unwrap(w).Error()
}

// errors.Is walks Unwrap and compares against a comparable target.
func errorsIs() (bool, bool, bool, bool) {
	_, err := strconv.ParseUint("x", 10, 64)
	w := wrapped{wrapped{err}}
	return errors.Is(w, strconv.ErrSyntax), errors.Is(w, strconv.ErrRange),
		errors.Is(err, strconv.ErrSyntax), errors.Is(nil, strconv.ErrSyntax)
}

// errors.As: gc finds the *NumError two wraps down; the machine reaches
// reflectlite.TypeOf in errors.As and refuses by name (frontier).
func errorsAs() (bool, string) {
	_, err := strconv.ParseUint("x", 10, 64)
	w := wrapped{wrapped{err}}
	var ne *strconv.NumError
	if errors.As(w, &ne) {
		return true, ne.Func + ":" + ne.Num
	}
	return false, ""
}

func main() {
	println(errorsUnwrap())
	println(errorsIs())
	println(errorsAs())
}
