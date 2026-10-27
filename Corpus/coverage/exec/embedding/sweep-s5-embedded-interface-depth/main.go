package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// An EMBEDDED INTERFACE reached through more than one hop: struct → struct →
// interface (the record's path then its `.iface` target re-dispatched on the
// field's value), the method VALUE over a nil field at depth 2 (gc panics at
// the bind, before the call), an embedded IMPORTED interface (`fmt.Stringer`)
// with a local dynamic value, the interface behind a pointer embed, and the
// method EXPRESSION whose promotion target is the embedded interface.

import "fmt"

type speaker interface{ Speak() string }

type dog struct{}

func (dog) Speak() string { return "woof" }

type kennel struct{ speaker }
type farm struct{ kennel }

func depth2Dispatch() string {
	f := farm{kennel{dog{}}}
	var s speaker = f // farm's set holds Speak through kennel.speaker
	var x any = &f
	_, ok := x.(speaker)
	r := s.Speak() + "/" + f.Speak()
	if ok {
		r += "/ptr"
	}
	return r
}

func depth2NilMethodValue() (out string) {
	defer func() {
		if r := recover(); r != nil {
			out = "bound:" + out + "/recovered"
		}
	}()
	var f farm // kennel.speaker is nil
	out = "pre"
	m := f.Speak // the bind reads the nil interface's method: panics HERE
	out = "post"
	return m()
}

type named struct{ n int }

func (v named) String() string {
	if v.n == 3 {
		return "named3"
	}
	return "named?"
}

type labelled struct{ fmt.Stringer }

func embeddedImportedInterface() string {
	l := labelled{named{n: 3}}
	var s fmt.Stringer = l // satisfies the imported interface through the embedded one
	return s.String() + "/" + l.String()
}

type pkennel struct{ *kennel }

func pointerThenInterface() (out string) {
	k := &kennel{dog{}}
	p := pkennel{k}
	var s speaker = p // walk the pointer hop, then re-dispatch on the field
	a := s.Speak()
	k.speaker = nil // the box holds p's pointer: the next dispatch finds the nil field
	var t speaker = p
	defer func() {
		if recover() != nil {
			out = a + "/nil-field-panic"
		}
	}()
	out = a + "/" + t.Speak()
	return out
}

func methodExpressionIfaceTarget() string {
	e := kennel.Speak // a func(kennel) string whose target is the embedded interface
	return e(kennel{dog{}})
}

func main() {
	depth2Dispatch()
	depth2NilMethodValue()
	embeddedImportedInterface()
	pointerThenInterface()
	methodExpressionIfaceTarget()
}
