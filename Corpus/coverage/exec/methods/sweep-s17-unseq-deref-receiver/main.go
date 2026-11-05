package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-001's line, cell B4.5): a POINTER-receiver method called on an
// explicitly dereferenced, parenthesised pointer — `(*p).bump()` — inside
// a statement the unseq lowering admits as a graph (a sibling call or
// observable occurrence beside it). The emitter's unseq lowering carries
// the implicit receiver address `&(*p)` as an `addr-of-deref` evaluation
// occurrence (BUG-056's eager nil-check op), which the decoder's unseq
// fragment does not admit, so the WHOLE wire is refused with status
// `error` where gc runs the program (BUG-391, found by this sweep — three
// rows born RED; the refusal is of the WHOLE wire, so the green controls —
// the same spelling alone on the legacy path, and the value-receiver twin
// `(*p).sum()` beside a pointer-receiver call — live in
// methods/sweep-s17-selector-forms).
// Expected = gc go1.26.5.

type pt struct{ x, y int }

func (p pt) sum() int   { return p.x + p.y }
func (p *pt) bump() int { p.x++; return p.x }

// red: a value-receiver call then the deref-paren pointer-receiver call
func derefParenReceiverBesideCall() int {
	p := &pt{1, 1}
	return (*p).sum()*10 + (*p).bump() // 22
}

// red: two pointer-receiver calls, the second through (*p)
func derefParenReceiverTwoCalls() int {
	p := &pt{1, 1}
	return p.bump()*10 + (*p).bump() // 23
}

// red: a sibling deref read first, then the deref-paren receiver
func derefParenReceiverAfterSiblingDeref() int {
	p := &pt{1, 1}
	q := &pt{5, 5}
	return (*q).x*10 + (*p).bump() // 52
}

func main() {
	println(derefParenReceiverBesideCall(), derefParenReceiverTwoCalls(), derefParenReceiverAfterSiblingDeref())
}
