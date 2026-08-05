package main

// recover() inside a PROMOTED method reached through a synthesized
// forwarding wrapper (dynamic dispatch on an embedding type). gc's rule
// (runtime/panic.go, gorecover): "there must be exactly one non-wrapper
// frame between gopanic and gorecover" — compiler-synthesized wrappers
// are TRANSPARENT to the recover walk (abi.FuncIDWrapper). The machine's
// synthesized promotion wrappers (design note 2026-08-05 D1.3) are
// ordinary call frames, so recover() inside the promoted method used to
// return nil: a silent value divergence (rwSilentValueEmbed) and a
// status-level flip (rwStatusValueEmbed). Pinned red-first by the
// arc-final audit (F1, 2026-08-06); the wrapper-transparency fix flips
// them. Controls pin the shapes that already agree — direct interface
// dispatch, concrete promoted call (call-site receiver adjustment),
// method values, and chain-JOINING through the same wrapper — so the fix
// cannot over-rotate.

type rwRec interface {
	rw() int
}

type rwInner struct{}

// The promoted method: recovers when (and only when) it is the deferred
// function of a panicking goroutine — through a wrapper in the pinned
// shapes.
func (rwInner) rw() int {
	if recover() != nil {
		return 1
	}
	return 0
}

type rwOuter struct{ rwInner }

type rwOuterPtr struct{ *rwInner }

type rwOuterIface struct{ rwRec }

// SILENT VALUE DIVERGENCE (the audit's decisive probe): Go recovers
// inside the promoted method, so the outer recover sees nil and out
// stays 0. An opaque wrapper frame makes the inner recover return nil,
// the panic keeps unwinding, and the OUTER recover fires: out = 100.
func rwSilentValueEmbed() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i rwRec = rwOuter{}
	defer i.rw()
	panic("boom")
}

// STATUS-LEVEL FLIP: no outer recover. Go: the deferred promoted method
// recovers, the function returns 0 (status ok). Opaque wrapper: the
// panic is unrecovered (status panic).
func rwStatusValueEmbed() int {
	var i rwRec = rwOuter{}
	defer i.rw()
	panic("x")
}

// Embedded-POINTER promotion path.
func rwSilentPointerEmbed() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i rwRec = rwOuterPtr{&rwInner{}}
	defer i.rw()
	panic("boom")
}

// Embedded-INTERFACE-field promotion path.
func rwSilentIfaceEmbed() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i rwRec = rwOuterIface{rwInner{}}
	defer i.rw()
	panic("boom")
}

// CONTROL: interface dispatch to a method DECLARED on the dynamic type
// (no wrapper). Agrees today; must stay agreeing.
func rwCtlDirectIface() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i rwRec = rwInner{}
	defer i.rw()
	panic("boom")
}

// CONTROL: concrete promoted call — call-site receiver adjustment, no
// wrapper frame.
func rwCtlConcretePromoted() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	o := rwOuter{}
	defer o.rw()
	panic("boom")
}

// CONTROL: method value of the promoted method.
func rwCtlMethodValue() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	o := rwOuter{}
	f := o.rw
	defer f()
	panic("boom")
}

type rwJoin struct{}

func (rwJoin) rw() int {
	panic("second")
}

type rwJoinOuter struct{ rwJoin }

// CONTROL: chain-JOINING through the same wrapper — a promoted method
// that PANICS while draining defers on the panic path. The wrapper frame
// is on the join path, which the audit verified correct; pin it so the
// recover-walk fix cannot disturb it.
func rwCtlChainJoin() (out int) {
	defer func() {
		if recover() != nil {
			out = 1
		}
	}()
	var i rwRec = rwJoinOuter{}
	defer i.rw()
	panic("first")
}
