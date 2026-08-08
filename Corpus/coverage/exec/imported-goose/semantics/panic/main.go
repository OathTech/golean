// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/panic.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func shouldPanic() {
	panic("bad")
}

// --- GoLean harness ---
// Authored wrapper.

func goleanShouldPanic() int {
	shouldPanic()
	return 0
}

func main() {}
