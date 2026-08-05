package main

// Frame-entry panics must be RECOVERABLE: dynamic dispatch on a nil
// interface (or the auto-deref of a nil pointer box) panics inside the
// machine's frame-entry step, and a deferred recover in the CALLING frame
// catches it — Go's ordinary panic semantics. Pinned because the machine
// used to throw these as raw (unrecoverable) errors: correct panic STATUS
// on unrecovered programs, wrong on recovering ones (found via the
// interface-method-value-nil pin, general-coverage slice 2 stage 5).

type recNilIface interface {
	m() int
}

type recNilImpl struct {
	n int
}

func (v recNilImpl) m() int {
	return v.n
}

func recoverNilInterfaceDispatch() (r int) {
	defer func() {
		if recover() != nil {
			r = 7
		}
	}()
	var x recNilIface
	return x.m()
}

func recoverNilPointerBoxDispatch() (r int) {
	defer func() {
		if recover() != nil {
			r = 8
		}
	}()
	var p *recNilImpl
	var x recNilIface = p
	return x.m()
}
