package main

// A DEFERRED interface method call whose dynamic dispatch panics at frame
// ENTRY (a nil pointer box auto-dereferencing for a value-receiver method)
// is an ordinary panic of the deferred call's INVOCATION: recoverable by
// an earlier-registered defer on the explicit-return drain and the
// fall-through drain, and DURING an unwinding panic it JOINS the chain —
// recover() returns the NEWEST panic (the runtime error), not the
// original payload. (Audit F1+F5, 2026-08-05: the machine threw these as
// unrecoverable errors — status "panic" on programs Go completes.)

type drainIface interface {
	m() int
}

type drainImpl struct {
	n int
}

func (v drainImpl) m() int {
	return v.n
}

func deferredEntryPanicReturn() (r int) {
	defer func() {
		if recover() != nil {
			r = 43
		}
	}()
	var p *drainImpl
	var x drainIface = p
	defer x.m()
	return 1
}

func drainHelper(out *int) {
	defer func() {
		if recover() != nil {
			*out = 55
		}
	}()
	var p *drainImpl
	var x drainIface = p
	defer x.m()
}

func deferredEntryPanicFallthrough() int {
	out := 0
	drainHelper(&out)
	return out
}

func deferredEntryPanicDuringPanic() (r int) {
	defer func() {
		rec := recover()
		if rec == nil {
			r = 0
			return
		}
		if s, ok := rec.(string); ok && s == "boom" {
			r = 1
			return
		}
		r = 66
	}()
	var p *drainImpl
	var x drainIface = p
	defer x.m()
	panic("boom")
}
