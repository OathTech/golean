// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/mutualrec/mutualrec.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func A() { // ERROR cycle in dependencies
	B()
}

func B() {
	A()
}

// --- GoLean harness ---
// Authored wrapper: the mutually recursive pair. (Correction,
// phase-C fix round 2026-08-08: at the pinned rev this is a POSITIVE
// gold-translated goose example — the upstream "// ERROR cycle in
// dependencies" comment is vestigial; NOT a parity delta.) Calling
// either function diverges by construction, so the wrapper takes
// their function VALUES only; the observable is that lowering works.

func goleanMutualRec() int {
	f := A
	g := B
	_ = f
	_ = g
	return 1
}

func main() {}
