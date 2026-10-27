package main

import (
	"errors"
	"fmt"
)

// Sweep S12 — the abort line for DEFINED-type and error-valued payloads
// (matrix cells A29, A38–A44, A47, A48, A52, J01, J04, J07; lane
// sweep/s12-panic-recover, 2026-10-27). gc's preprintpanics calls
// `Error()` (then `String()`) on the payload and prints the returned string
// (runtime/panic.go:702–730); a defined type with neither prints
// printanycustomtype's `main.T(v)`. The machine: `phaseMark` and the
// preprint phase (Machine.lean), `renderPanicRewrite`'s `main.T(v)` arm.

type t8 int8

type u64 uint64

func abortDefinedInt8() { panic(t8(-3)) }

func abortDefinedUint64() { panic(u64(18446744073709551615)) }

// A pointer-receiver Error() on a non-nil POINTER payload (the method is in
// *ptrErr's method set).
type ptrErr struct{ m string }

func (e *ptrErr) Error() string { return e.m }

func abortPtrRecvErrorOnPtr() { panic(&ptrErr{"ptr-text"}) }

// A value-receiver Error() on a POINTER payload (*valErr's method set
// contains valErr's methods).
type valErr struct{ m string }

func (e valErr) Error() string { return e.m }

func abortValueRecvErrorOnPtr() { panic(&valErr{"val-text"}) }

// The spec's `Error("cannot parse")` shape: a defined STRING type with Error().
type strErr string

func (e strErr) Error() string { return string(e) }

func abortDefinedStringError() { panic(strErr("cannot parse")) }

// A struct with a value-receiver Error().
type structErr struct{ code int }

func (s structErr) Error() string {
	if s.code > 0 {
		return "struct-err-pos"
	}
	return "struct-err-nonpos"
}

func abortStructError() { panic(structErr{1}) }

// The library's own error types: errors.New (source-through
// *errors.errorString) and fmt.Errorf without %w (the frontend's shim type).
func abortErrorsNew() { panic(errors.New("from-errors-new")) }

func abortFmtErrorf() { panic(fmt.Errorf("fmt-%d", 7)) }

// A custom error wrapping another: Error() composes the inner text.
type wrapErr struct {
	op    string
	inner error
}

func (w *wrapErr) Error() string { return w.op + ": " + w.inner.Error() }

func (w *wrapErr) Unwrap() error { return w.inner }

func abortWrappedError() { panic(&wrapErr{"open", errors.New("base")}) }

// A String() that panics: gc's fatal `panic while printing panic value`.
type stringerPanics int

func (stringerPanics) String() string { panic("in-string") }

func abortStringerPanics() { panic(stringerPanics(1)) }

// An Error() returning the EMPTY string: `panic: ` and nothing else; the
// output prefix keeps the row's reason non-empty.
type emptyErr struct{}

func (emptyErr) Error() string { return "" }

func abortErrorEmptyText() {
	print("empty-error-text\n")
	panic(emptyErr{})
}

// A payload boxed from a NAMED INTERFACE variable (a local Stringer).
type stringer interface{ String() string }

type st int

func (st) String() string { return "stringer-text" }

func abortViaStringerIface() {
	var s stringer = st(1)
	panic(s)
}

// A pointer-receiver String() is NOT in the value's method set: the value
// payload prints printanycustomtype's `main.T(v)` (the Stringer twin of
// panic-preprint/ptr-method-not-in-value-set).
type ptrStringer int

func (*ptrStringer) String() string { return "never" }

func abortPtrStringerOnValue() { panic(ptrStringer(3)) }

// Error() with the WRONG signature (`Error() int`) is not `error`: gc
// prints the `main.T(v)` form.
type wrongErr int

func (wrongErr) Error() int { return 1 }

func rewriteErrorWrongSig() { panic(wrongErr(3)) }

// error through an EMBEDDED INTERFACE field: the promoted Error() is called.
type carrier struct{ error }

func rewriteEmbeddedErrorIface() { panic(carrier{errors.New("embedded-text")}) }

// Error() on a generic type instantiation.
type box[T any] struct{ v T }

func (b box[T]) Error() string { return "box-text" }

func rewriteGenericError() { panic(box[int]{1}) }

func main() {}
