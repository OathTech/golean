package main

// Born pins for native method promotion (G-P, design note
// docs/2026-09-28_gp-method-promotion-design.md §5 S0): the DYNAMIC
// promotion surface — interface dispatch, interface method values and
// method expressions over PROMOTED methods — in the shapes the corpus
// did not pin before the wrappers are replaced by promotion records.
// Each subject distinguishes WHEN and WHERE the embedding path is
// walked (design §2 S3: at the entry of the dispatched call — in the
// child for `go`, at the drain for `defer`, at each call for an
// interface method value), where a nil in the path panics (S4), and
// that recover() in a promoted method reached through `defer S.M(s)`
// recovers (S6/S7). Every expected value was observed under go1.26.5
// (plain and -race) before the row was added.

type pdGetter interface {
	Get() int
}

type pdRecorder interface {
	Rec()
}

type pdIncer interface {
	Inc()
}

type pdInner struct{ v int }

// VALUE receiver: promoted through a value embed into both method sets,
// through a pointer embed into both method sets.
func (e pdInner) Get() int { return e.v }

var pdSink int

func (e pdInner) Rec() { pdSink = e.v }

// POINTER receiver: promoted through a value embed into *S's set only.
func (e *pdInner) Inc() { e.v++ }

type pdOuter struct{ pdInner }

type pdOuterPtr struct{ *pdInner }

type pdOuterIface struct{ pdGetter }

// `go i.Get()` over a nil embedded *pdInner with a VALUE method: the
// receiver copy out of nil panics in the CHILD (gc's wrapper runs in
// the new goroutine), so the parent's deferred recover never sees it
// and the program aborts. A walk in the parent would recover: 100.
func pdGoNilPtrEmbed() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i pdGetter = pdOuterPtr{}
	go i.Get()
	<-make(chan int)
	return 0
}

// `go i.Get()` over a nil embedded INTERFACE field: the re-dispatch on
// the nil field panics in the child.
func pdGoNilIfaceEmbed() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i pdGetter = pdOuterIface{}
	go i.Get()
	<-make(chan int)
	return 0
}

// `defer i.Get()` over a nil embedded *pdInner: the path is walked at
// the DRAIN, so the statement after the defer runs (pdSink = 7) before
// the panic; a walk at registration would leave pdSink at 0.
func pdDeferNilPath() (out int) {
	pdSink = 0
	defer func() {
		if recover() != nil {
			out = pdSink + 100
		}
	}()
	var i pdGetter = pdOuterPtr{}
	defer i.Get()
	pdSink = 7
	return 0
}

// `defer i.Rec()` over a *pdOuter box mutated after registration: the
// promoted value receiver is copied out of the box's pointee at the
// drain, so the deferred call sees v = 2.
func pdDeferBoxMutated() int {
	pdSink = 0
	o := &pdOuter{pdInner{1}}
	var i pdRecorder = o
	func() {
		defer i.Rec()
		o.pdInner.v = 2
	}()
	return pdSink
}

// Control: the STATIC `defer o.Rec()` evaluates the receiver (the
// embedded value) at the defer statement: v = 1.
func pdDeferStaticControl() int {
	pdSink = 0
	o := &pdOuter{pdInner{1}}
	func() {
		defer o.Rec()
		o.pdInner.v = 2
	}()
	return pdSink
}

// `defer i.Rec()` over a *pdOuterPtr box whose embedded POINTER is
// replaced after registration: the hop is loaded at the drain (3).
func pdDeferPtrHopReplaced() int {
	pdSink = 0
	o := &pdOuterPtr{&pdInner{1}}
	var i pdRecorder = o
	func() {
		defer i.Rec()
		o.pdInner = &pdInner{3}
	}()
	return pdSink
}

// An interface METHOD VALUE saves the box, not the promoted receiver:
// the path is walked at each call (spec#Method_values), so f() sees
// each mutation of the pointee.
func pdIfaceMethodValueLate() int {
	o := &pdOuter{pdInner{1}}
	var i pdGetter = o
	f := i.Get
	o.pdInner.v = 2
	a := f()
	o.pdInner.v = 5
	b := f()
	return a*10 + b
}

// The same through an embedded POINTER hop replaced between calls.
func pdIfaceMethodValuePtrHop() int {
	o := &pdOuterPtr{&pdInner{1}}
	var i pdGetter = o
	f := i.Get
	o.pdInner = &pdInner{4}
	return f()
}

// recover() inside a promoted method reached through a deferred METHOD
// EXPRESSION `pdRw.rw(s)`: gc's method expression names the promotion
// wrapper (abi.FuncIDWrapper, skipped by the recover walk), so the
// promoted rw recovers, the outer recover sees nil, and out stays 0.
type pdRwInner struct{}

func (pdRwInner) rw() int {
	if recover() != nil {
		return 1
	}
	return 0
}

type pdRw struct{ pdRwInner }

func pdDeferMethodExprRecover() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	defer pdRw.rw(pdRw{})
	panic("boom")
}

// Status form: no outer recover — Go returns normally (ok 0).
func pdDeferMethodExprRecoverStatus() int {
	defer pdRw.rw(pdRw{})
	panic("x")
}

// A nil *pdOuter box dispatching the POINTER method Inc promoted through
// a VALUE embed: the receiver is &s.pdInner, and taking the address of
// a field of nil panics (spec#Address_operators), inside Inc's entry.
func pdNilBoxPtrMethodValueEmbed() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var s *pdOuter
	var i pdIncer = s
	i.Inc()
	return 1
}

func main() {}
