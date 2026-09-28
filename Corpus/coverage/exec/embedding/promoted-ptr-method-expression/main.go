package main

// Born pins for native method promotion (G-P, design note
// docs/2026-09-28_gp-method-promotion-design.md §2 S7): the POINTER
// method expression `(*S).M` over a method PROMOTED into S's value
// method set. On main the promotion wrapper takes S by value and the
// frontend refuses the `(*S).M` form (deref adapter not modeled,
// ledger FR-3); after P a method expression names the promotion record,
// whose receiver adjustment dereferences, so the refusal retires for
// PROMOTED entries (declared value methods stay on FR-3). Expected
// values observed under go1.26.5, plain and -race.

type pdInner struct{ v int }

func (e pdInner) Get() int { return e.v }

type pdOuter struct{ pdInner }

type pdRwInner struct{}

func (pdRwInner) rw() int {
	if recover() != nil {
		return 1
	}
	return 0
}

type pdRw struct{ pdRwInner }

// The POINTER method expression `(*pdRw).rw` over the promoted VALUE
// method: gc's (*pdRw).rw wrapper dereferences its argument and is a
// wrapper frame too, so the promoted rw recovers (out stays 0).
func pdDeferPtrMethodExprRecover() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	defer (*pdRw).rw(&pdRw{})
	panic("boom")
}

// `(*pdOuter).Get` over the promoted VALUE method, called directly:
// the argument's pointee is read at the call (2, not 1).
func pdPtrMethodExprPromotedValue() int {
	o := &pdOuter{pdInner{1}}
	g := (*pdOuter).Get
	o.pdInner.v = 2
	return g(o)
}

func main() {}
