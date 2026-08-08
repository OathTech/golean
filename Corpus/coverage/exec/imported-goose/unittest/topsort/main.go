// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/topsort.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// Make sure that goose tracks dependencies and emits A's Coq definition before
// B's.

type B struct {
	a []A
}

type A struct {
}

// --- GoLean harness ---
// Authored wrapper.

// topsort.go is a TYPE-ORDER test (zero functions upstream): the
// wrapper constructs the dependent pair.
func goleanTopsort() int {
	x := B{a: []A{{}, {}}}
	return len(x.a)
}

func main() {}
