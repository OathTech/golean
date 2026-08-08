package main

// Method VALUE selection through a nil pointer with a VALUE receiver
// panics at SELECTION time (spec §Method values: p.get with value
// receiver evaluates (*p) and saves the copy when the method value is
// bound) — the bound function is never called here, so the panic can
// only come from the selection itself. Complements
// methods/nil-pointer-method-value (POINTER receiver: selection is
// fine, nil flows to the receiver). Green cell from the external Codex
// review 2026-08-08 (docs/2026-08-08_semantic-divergence-review.md §2).

type nilSelNode struct{ n int }

func (v nilSelNode) get() int { return v.n }

func nilValueReceiverMethodValue() int {
	var p *nilSelNode
	f := p.get // panics HERE, before any call
	_ = f
	return 1 // unreachable in Go
}

func main() {
	nilValueReceiverMethodValue()
}
