package main

// Value vs pointer method-value receiver capture on ONE type, observed
// side by side: binding a VALUE-receiver method value copies the
// receiver at bind time (later mutation invisible), while a
// POINTER-receiver method value captures the pointer (later mutation
// visible). Complements methods/method-value-copy and
// methods/pointer-method-value-live, which pin the halves on separate
// types. Green cell from the external Codex review 2026-08-08
// (docs/2026-08-08_semantic-divergence-review.md §2).

type captureCell struct{ n int }

func (c captureCell) valGet() int { return c.n }

func (c *captureCell) ptrGet() int { return c.n }

func methodValueCaptureVsPointer() int {
	c := captureCell{n: 1}
	vf := c.valGet // copies c (n=1) now
	pf := c.ptrGet // captures &c
	c.n = 7
	return vf()*10 + pf() // 17: copy stays 1, pointer sees 7
}

func main() {
	methodValueCaptureVsPointer()
}
