package main

// BUG-124 FIXED (2026-10-12, lane core/uintptr-repair-impl-1012): `uintptr`
// is a DISTINCT integer kind on the machine (`IntKind.uintptr`,
// GoLean/GoCore/Value.lean), so the frontend's by-name refusal of every
// identity-bearing position (the retired uintptrid.go — the REFUSE half of
// [USER] Mike 2026-10-12's D6 — refuse now, repair soon —
// relayed; the repair's shape [USER] Mike 2026-10-12, items 1 and 3-6 approved, item
// 4 = docs/2026-10-12_uintptr-repair-design.md D1–D5, relayed) is gone.
// This pins the retirement from the frontend's side: the release-trust
// review's six R1 probe shapes and the method-set shapes EXPORT with a body
// (no per-declaration quarantine). The frontend cannot evaluate them; gc's
// answers are the corpus's (Corpus/coverage/exec/interfaces/uintptr-identity/,
// eleven PASS rows on BUG-124's Cases line).

import "testing"

var uintptrIdentityShapes = map[string]string{
	// --- the review's six probes ---
	"r1-assert": `package main
func subject() bool { var x any = uintptr(1); _, ok := x.(uint64); return ok }
`,
	"r1-equal": `package main
func subject() bool { return any(uintptr(1)) == any(uint64(1)) }
`,
	"r1-switch": `package main
func subject() int {
	var x any = uintptr(1)
	switch x.(type) {
	case uint64:
		return 64
	case uintptr:
		return 1
	}
	return 0
}
`,
	"r1-map-key": `package main
func subject() int { return len(map[any]int{uintptr(1): 7, uint64(1): 9}) }
`,
	"r1-slice-assert": `package main
func subject() bool { var x any = []uintptr{1}; _, ok := x.([]uint64); return ok }
`,
	"r1-pointer-assert": `package main
func subject() bool { n := uintptr(1); var x any = &n; _, ok := x.(*uint64); return ok }
`,
	// --- the method-set shapes: a named type whose method set mentions uintptr ---
	"method-param": `package main
type T struct{}
func (T) M(x uintptr) {}
type U interface{ M(uint64) }
func subject() bool { var v any = T{}; _, ok := v.(U); return ok }
`,
	"method-result": `package main
type T struct{}
func (T) M() uintptr { return 7 }
type U interface{ M() uint64 }
func subject() bool { var v any = T{}; _, ok := v.(U); return ok }
`,
	"promoted-method-set": `package main
type T struct{}
func (T) P() uintptr { return 1 }
type Out struct{ T }
func subject() int { var x any = Out{}; _ = x; return 1 }
`,
	"interface-requirement-target": `package main
type P interface{ P() uintptr }
func subject() bool { var x any = 1; _, ok := x.(P); return ok }
`,
}

func TestUintptrIdentityShapesExport(t *testing.T) {
	for name, src := range uintptrIdentityShapes {
		t.Run(name, func(t *testing.T) {
			program, err := emitSource(t, src)
			if err != nil {
				t.Fatalf("export must succeed: %v", err)
			}
			if r := stubReason(t, program, "subject"); r != "" {
				t.Fatalf("an identity-bearing uintptr position must LOWER since BUG-124's repair (the machine keeps the kind distinct), got the refusal %q", r)
			}
		})
	}
}
