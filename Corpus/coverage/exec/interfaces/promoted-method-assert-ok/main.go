package main

// BUG-007 (unmodeled method promotion) on the ASSERT path: satisfaction via a
// PROMOTED method made the comma-ok boolean silently FALSE where Go says true
// (pre-merge audit 2026-07-31, finding 5 — which falsified BUG-007's
// "never a wrong answer" claim). The machine now fails CLOSED here instead of
// answering false; this case is a pinned RED until promotion is modeled.

type promoIface interface{ M() int }

type promoInner struct{ n int }

func (i promoInner) M() int { return i.n }

type promoOuter struct{ promoInner }

func promotedMethodAssertOk() int {
	var a any = promoOuter{promoInner{n: 5}}
	_, ok := a.(promoIface)
	if ok {
		return 1
	}
	return 0
}
