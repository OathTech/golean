package main

// Promoted METHOD VALUES pin the receiver-adjustment MOMENT (design note
// D1: adjustment happens at method-value creation, not at call):
//   - snapshot: value receiver reached through an embedded pointer — the
//     receiver is COPIED at value-creation time, so a later reassignment
//     of the embedded pointer or mutation through it is invisible.
//   - live: pointer receiver reached through value embedding — the value
//     captures the CELL address, so later mutation IS visible.

type snapInner struct {
	n int
}

func (v snapInner) val() int {
	return v.n
}

type snapOuter struct {
	*snapInner
}

func promotedMethodValueSnapshot() int {
	a := &snapInner{n: 1}
	b := &snapInner{n: 2}
	o := snapOuter{snapInner: a}
	f := o.val
	o.snapInner = b
	a.n = 7
	return f()
}

type snapPInner struct {
	n int
}

func (p *snapPInner) pval() int {
	return p.n
}

type snapPOuter struct {
	snapPInner
}

func promotedPtrMethodValueLive() int {
	o := snapPOuter{snapPInner: snapPInner{n: 1}}
	f := o.pval
	o.snapPInner.n = 5
	return f()
}
