// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Method value creation x.M evaluates x once, at creation — the receiver from a call
// (pointer receiver, value receiver copied at creation, interface), invoked twice; the
// method expression with a call argument; an index-with-call receiver; a deref of a call;
// in a closure and in a generic function.

package main

var cnt int

type T struct{ n int }

func (t *T) Inc() int { t.n++; return t.n }
func (t T) Get() int  { return t.n }

type I interface{ Inc() int }

func pf() *T { cnt++; return &T{n: 10} }
func gs() T  { cnt++; return T{n: 20} }
func fi() I  { cnt++; return &T{n: 30} }
func g() int { cnt++; return 1 }

func ptrRecvCallValue() int {
	cnt = 0
	m := pf().Inc
	m()
	v := m()
	return cnt*100 + v
}

func valueRecvCallValue() int {
	cnt = 0
	m := gs().Get
	a := m()
	b := m()
	return cnt*100 + a + b
}

func ifaceRecvCallValue() int {
	cnt = 0
	m := fi().Inc
	m()
	v := m()
	return cnt*100 + v
}

func methodExprCallArg() int {
	cnt = 0
	v := (*T).Inc(pf())
	w := T.Get(gs())
	return cnt*100 + v + w
}

func indexCallRecvValue() int {
	cnt = 0
	s := []*T{{n: 1}, {n: 40}}
	m := s[g()].Inc
	m()
	v := m()
	return cnt*100 + v
}

func derefCallRecvValue() int {
	cnt = 0
	m := (*pf()).Get
	a := m()
	b := m()
	return cnt*100 + a + b
}

func closureMv() int {
	cnt = 0
	r := 0
	inner := func() {
		m := pf().Inc
		m()
		r = m()
	}
	inner()
	return cnt*100 + r
}

type incer interface{ Inc() int }

func mvGeneric[X incer](mk func() X) int {
	m := mk().Inc
	m()
	return m()
}

func genericMv() int {
	cnt = 0
	v := mvGeneric(pf)
	return cnt*100 + v
}

func main() {
	ptrRecvCallValue()
	valueRecvCallValue()
	ifaceRecvCallValue()
	methodExprCallArg()
	indexCallRecvValue()
	derefCallRecvValue()
	closureMv()
	genericMv()
}
