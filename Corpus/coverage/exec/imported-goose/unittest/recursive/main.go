// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/recursive.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func recur() {
	recur()
}

type R struct {
}

func (r *R) recurMethod() {
	r.recurMethod()
}

type Other struct {
	*RecursiveEmbedded
}

type RecursiveEmbedded struct {
	Other
}

func (r *RecursiveEmbedded) recurEmbeddedMethod() {
	r.Other.recurEmbeddedMethod()
}

// --- GoLean harness ---
// Authored wrapper.

// The recursive functions/methods diverge if called; the wrapper takes
// values/constructs types only (observable = lowering works, incl. the
// mutually-embedded Other/RecursiveEmbedded type cycle).
func goleanRecursive() int {
	f := recur
	_ = f
	r := &R{}
	_ = r
	return 1
}

func main() {}
